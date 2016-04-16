// TODO: Kill this after specialization is stablized.

impl NumCast for u128 {
    fn from<T: ToPrimitive + 'static>(_: T) -> Option<u128> {
        panic!("cannot use this outside of nightly rust yet");
    }
}

impl NumCast for i128 {
    fn from<T: ToPrimitive + 'static>(_: T) -> Option<i128> {
        panic!("cannot use this outside of nightly rust yet");
    }
}

