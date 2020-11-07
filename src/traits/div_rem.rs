pub trait DivRem<Rhs=Self> {
    type DivOutput;
    type RemOutput;

    fn div_rem(self, rhs: Rhs) -> (Self::DivOutput, Self::RemOutput);
}
