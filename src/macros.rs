macro_rules! bitpos {
    ($idx:expr) => {{
        let idx = $idx;
        (idx >> 6, idx & 63)
    }};
}

macro_rules! msb {
    ($val:expr) => {{
        let val = $val;
        val.cast_signed() < 0
    }};
}

pub(crate) use bitpos;
pub(crate) use msb;
