// A Curve41417 field element representation.
use serialize::hex::ToHex;
use std::default::Default;
use std::fmt::{Show, Formatter, Result};

use bytes::{B416, Bytes, Uniformity};
use sbuf::{StdHeapAllocator, SBuf};
use utils;


static FE_SIZE: uint = 26;

static ONE: [i64, ..FE_SIZE] = [
    1, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0];


#[deriving(Clone)]
pub struct FieldElem {
    elem: SBuf<StdHeapAllocator, i64>
}

impl FieldElem {
    pub fn new() -> FieldElem {
        FieldElem::zero()
    }

    pub fn zero() -> FieldElem {
        FieldElem {
            elem: SBuf::new_zero(FE_SIZE)
        }
    }

    pub fn one() -> FieldElem {
        FieldElem {
            elem: SBuf::from_slice(ONE.as_slice())
        }
    }

    // Return a reference to the limb at index `index`. Fails if
    // `index` is out of bounds.
    pub fn get<'a>(&'a self, index: uint) -> &'a i64 {
        self.elem.get(index)
    }

    // Return a mutable reference to the limb at index `index`. Fails
    // if `index` is out of bounds.
    pub fn get_mut<'a>(&'a mut self, index: uint) -> &'a mut i64 {
        self.elem.get_mut(index)
    }

    pub fn unpack(bytes: &B416) -> FieldElem {
        let mut n = FieldElem::new();

        for i in range(0u, 26) {
            *n.get_mut(i) = *bytes.get(2 * i) as i64 +
                (*bytes.get(2 * i + 1) as i64 << 8);
        }
        *n.get_mut(25) &= 0x3fff; // mask top 2 bits
        n
    }

    pub fn pack(&self) -> B416 {
        let t = self.clone().reduce();
        let mut r: B416 = Bytes::new_zero();

        for i in range(0u, FE_SIZE) {
            *r.get_mut(2 * i) = (*t.get(i) & 0xff) as u8;
            *r.get_mut(2 * i + 1) = (*t.get(i) >> 8) as u8;
        }
        r
    }

    pub fn cswap(&mut self, cond: i64, other: &mut FieldElem) {
        utils::bytes_cswap::<i64>(cond,
                                  self.elem.as_mut_slice(),
                                  other.elem.as_mut_slice());
    }

    pub fn carry(&self) -> FieldElem {
        let mut r = self.clone();
        let mut c: i64;

        for i in range(0, r.len()) {
            *r.get_mut(i) += 1_i64 << 16;
            c = *r.get(i) >> 16;
            *r.get_mut((i + 1) * ((i < 25) as uint)) += c - 1 + 67 * (c - 1) *
                ((i == 25) as i64);
            *r.get_mut(i) -= c << 16;
        }
        r
    }

    // Fully reduce n mod 2^414 - 17
    pub fn reduce(&self) -> FieldElem {
        let mut r = self.clone().carry().carry().carry();
        let mut m = FieldElem::new();

        for _ in range(0, 3) {
            *m.get_mut(0) = *r.get(0) - 0xffef;
            for j in range(1u, 25) {
                *m.get_mut(j) = *r.get(j) - 0xffff - ((*m.get(j - 1) >> 16) & 1);
                *m.get_mut(j - 1) &= 0xffff;
            }
            *m.get_mut(25) = *r.get(25) - 0x3fff - ((*m.get(24) >> 16) & 1);
            *m.get_mut(24) &= 0xffff;
            let b = (*m.get(25) >> 16) & 1;
            *m.get_mut(25) &= 0xffff;
            r.cswap(1 - b, &mut m);
        }
        r
    }

    // Reduce n mod 2^416 - 68 and put limbs between [0, 2^16-1] through carry.
    // Requirement: 52 < n.len() <= 104
    pub fn reduce_weak_from_bytes<T: Bytes + Uniformity>(n: &T) -> FieldElem {
        let l = n.as_bytes().len() / 2;
        assert!(l > 26 && l <= 52);

        let mut r = FieldElem::new();

        for i in range(0u, 26) {
            *r.get_mut(i) = *n.get(2 * i) as i64 +
                (*n.get(2 * i + 1) as i64 << 8);
        }
        for i in range(26u, l) {
            *r.get_mut(i - 26) += (*n.get(2 * i) as i64 +
                                   (*n.get(2 * i + 1) as i64 << 8)) * 68;
        }

        r.carry().carry()
    }

    pub fn parity_bit(&self) -> u8 {
        let t = self.pack();
        *t.get(0) & 1
    }

    pub fn muli(&self, other: i16) -> FieldElem {
        let mut r = self.clone();

        for i in range(0, r.len()) {
            *r.get_mut(i) *= other as i64;
        }

        r.carry().carry()
    }

    pub fn square(&self) -> FieldElem {
        self.mul(self)
    }

    pub fn inv(&self) -> FieldElem {
        let mut r = self.clone();

        for i in range(0, 413).rev() {
            r = r.square();
            if i != 1 && i != 4 {
                r = r.mul(self);
            }
        }
        r
    }

    // i ** ((P - 1) / 2) = i ** (2 ** 413 - 9)
    pub fn pow4139(&self) -> FieldElem {
        let mut r = self.clone();

        for i in range(0, 412).rev() {
            r = r.square();
            if i != 3 {
                r = r.mul(self);
            }
        }
        r
    }

    // i ** ((P - 3) / 4) = i ** (2 ** 412 - 5)
    pub fn pow4125(&self) -> FieldElem {
        let mut r = self.clone();

        for i in range(0, 411).rev() {
            r = r.square();
            if i != 2 {
                r = r.mul(self);
            }
        }
        r
    }

    // i ** ((P + 1) / 4) = i ** (2 ** 412 - 4)
    pub fn pow4124(&self) -> FieldElem {
        let mut r = self.clone();

        for i in range(0, 411).rev() {
            r = r.square();
            if i != 0 && i != 1 {
                r = r.mul(self);
            }
        }
        r
    }
}

impl Add<FieldElem, FieldElem> for FieldElem {
    fn add(&self, other: &FieldElem) -> FieldElem {
        let mut r = self.clone();
        for i in range(0, r.len()) {
            *r.get_mut(i) += *other.get(i);
        }
        r
    }
}

impl Sub<FieldElem, FieldElem> for FieldElem {
    fn sub(&self, other: &FieldElem) -> FieldElem {
        let mut r = self.clone();
        for i in range(0, r.len()) {
            *r.get_mut(i) -= *other.get(i);
        }
        r
    }
}

impl Neg<FieldElem> for FieldElem {
    fn neg(&self) -> FieldElem {
        FieldElem::zero() - *self
    }
}

impl Mul<FieldElem, FieldElem> for FieldElem {
    fn mul(&self, other: &FieldElem) -> FieldElem {
        let mut u: i64;
        let mut r = FieldElem::new();

        for i in range(0u, 26) {
            u = 0;
            for j in range(0u, i + 1) {
                u += *self.get(j) * *other.get(i - j);
            }
            for j in range(i + 1, 26) {
                u += 68 * *self.get(j) * *other.get(i + 26 - j);
            }
            *r.get_mut(i) = u;
        }

        r.carry().carry()
    }
}

impl Default for FieldElem {
    fn default() -> FieldElem {
        FieldElem::new()
    }
}

impl Show for FieldElem {
    fn fmt(&self, f: &mut Formatter) -> Result {
        self.pack().fmt(f)
    }
}

impl ToHex for FieldElem {
    fn to_hex(&self) -> String {
        self.pack().to_hex()
    }
}

impl PartialEq for FieldElem {
    fn eq(&self, other: &FieldElem) -> bool {
        self.pack() == other.pack()
    }
}

impl Eq for FieldElem {
}

impl Collection for FieldElem {
    fn len(&self) -> uint {
        self.elem.len()
    }
}
