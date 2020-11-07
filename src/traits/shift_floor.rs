pub trait ShiftFloor where Self: Sized {
    type Output;

    fn shift_floor(self, shift: isize) -> Self::Output;

    fn floor(self) -> Self::Output { self.shift_floor(0) }
}
