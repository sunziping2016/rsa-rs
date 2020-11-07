use std::sync::mpsc::channel;
use std::thread;
use rand::distributions::{Distribution, Uniform};
use rand::distributions::uniform::SampleUniform;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use crate::traits::{Bits, One, IsPrimeMillerRabin, Zero};
use std::ops::{AddAssign, Add, Sub};

pub mod numbers;
pub mod traits;
pub mod macros;

pub fn find_prime_range<T>(low: &T, high: &T, num_prime_tests: u64, num_workers: usize) -> T
    where
        T: 'static + SampleUniform + Clone + Send + Bits + One + IsPrimeMillerRabin +
        for<'a> AddAssign<&'a T> + Ord + Zero + From<u64> + Into<u64>,
        for<'a> &'a T: Add<&'a T, Output=T> + Sub<&'a T, Output=T> {
    let (sender, receiver) = channel();
    let finished = Arc::new(AtomicBool::new(false));
    let three = &(&T::one() + &T::one()) + &T::one();
    let workers = (0..num_workers)
        .map(|_| {
            let low = low.clone();
            let high = high.clone();
            let three = three.clone();
            let finished = finished.clone();
            let sender = sender.clone();
            thread::spawn(move || {
                let between = Uniform::from(low..high.clone());
                let num_prime_tests = T::from(num_prime_tests);
                let mut rng = rand::thread_rng();
                while !finished.load(Ordering::Relaxed) {
                    let mut n = between.sample(&mut rng);
                    if match n.cmp(&three) {
                        std::cmp::Ordering::Less | std::cmp::Ordering::Equal =>
                            !n.is_one() && !n.is_zero(),
                        std::cmp::Ordering::Greater => {
                            if !n.get(0) {
                                n += &T::one();
                                if n > high {
                                    continue
                                }
                            }
                            let times = std::cmp::min(&n - &three, num_prime_tests.clone()).into();
                            n.is_prime_miller_rabin(times)
                        },
                    } {
                        let _ = sender.send(n);
                        finished.store(true, Ordering::Relaxed);
                        break;
                    }
                }
            })
        })
        .collect::<Vec<_>>();
    let prime = receiver.recv().unwrap();
    for worker in workers.into_iter() {
        worker.join().unwrap();
    }
    prime
}