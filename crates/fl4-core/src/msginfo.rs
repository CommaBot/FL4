//! `seL4_MessageInfo_t`: label 52 bits, capsUnwrapped 3, extraCaps 2,
//! length 7 (libsel4 shared_types.bf).

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct MessageInfo {
    pub label: u64,
    pub caps_unwrapped: u64,
    pub extra_caps: u64,
    pub length: u64,
}

impl MessageInfo {
    pub fn from_word(w: u64) -> MessageInfo {
        MessageInfo {
            label: w >> 12,
            caps_unwrapped: (w >> 9) & 0x7,
            extra_caps: (w >> 7) & 0x3,
            length: w & 0x7f,
        }
    }

    /// `messageInfoFromWord`: the kernel clamps the length to the maximum.
    pub fn from_word_clamped(w: u64) -> MessageInfo {
        let mut m = MessageInfo::from_word(w);
        if m.length > fl4_abi::consts::MSG_MAX_LENGTH {
            m.length = fl4_abi::consts::MSG_MAX_LENGTH;
        }
        m
    }

    pub fn to_word(self) -> u64 {
        ((self.label & 0x000f_ffff_ffff_ffff) << 12)
            | ((self.caps_unwrapped & 0x7) << 9)
            | ((self.extra_caps & 0x3) << 7)
            | (self.length & 0x7f)
    }

    pub fn new(label: u64, caps_unwrapped: u64, extra_caps: u64, length: u64) -> MessageInfo {
        MessageInfo { label, caps_unwrapped, extra_caps, length }
    }
}
