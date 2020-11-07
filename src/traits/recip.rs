pub trait Recip {
    type Recip;

    fn recip(&self) -> Self::Recip;
}

pub trait RecipWithPrecision {
    type Recip;

    fn recip_with_precision(&self, precision: usize) -> Self::Recip;
}
