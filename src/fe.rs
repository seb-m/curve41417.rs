// A Curve41417 field element representation.
use std::default::Default;
use std::fmt::{Show, Formatter, Result};

use bytes::{B416, Bytes, Uniformity};
use utils;
use utils::ZeroMemory;


static FE_SIZE: uint = 26;

static ONE: [i64, ..FE_SIZE] = [
    1i64, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0];


pub struct FieldElem {
    elem: [i64, ..FE_SIZE]
}

impl FieldElem {
    pub fn new() -> FieldElem {
        FieldElem::zero()
    }

    pub fn zero() -> FieldElem {
        FieldElem {
            elem: [0i64, ..FE_SIZE]
        }
    }

    pub fn one() -> FieldElem {
        FieldElem {
            elem: ONE
        }
    }

    pub fn get_limb(&self, index: uint) -> i64 {
        self.elem[index]
    }

    pub fn set_limb(&mut self, index: uint, value: i64) {
        self.elem[index] = value;
    }

    pub fn unpack(bytes: &B416) -> FieldElem {
        let mut n = FieldElem::new();

        for i in range(0u, 26) {
            n.elem[i] = bytes[2 * i] as i64 + (bytes[2 * i + 1] as i64 << 8);
        }
        n.elem[25] &= 0x3fff; // mask top 2 bits
        n
    }

    pub fn pack(&self) -> B416 {
        let t = self.clone().reduce();
        let mut r: B416 = Bytes::new_zero();

        for i in range(0u, FE_SIZE) {
            r.as_mut_bytes()[2 * i] = (t.elem[i] & 0xff) as u8;
            r.as_mut_bytes()[2 * i + 1] = (t.elem[i] >> 8) as u8;
        }
        r
    }

    pub fn to_str_hex(&self) -> String {
        self.pack().to_str_hex()
    }

    fn cleanup(&mut self) {
        self.elem.zero_memory();
    }

    pub fn cswap(&mut self, cond: i64, other: &mut FieldElem) {
        utils::bytes_cswap::<i64>(cond, self.elem, other.elem);
    }

    pub fn carry(&self) -> FieldElem {
        let mut r = self.clone();
        let mut c: i64;

        for i in range(0, r.elem.len()) {
            r.elem[i] += 1_i64 << 16;
            c = r.elem[i] >> 16;
            r.elem[(i + 1) * ((i < 25) as uint)] += c - 1 + 67 * (c - 1) *
                ((i == 25) as i64);
            r.elem[i] -= c << 16;
        }
        r
    }

    // Fully reduce n mod 2^414 - 17
    pub fn reduce(&self) -> FieldElem {
        let mut r = self.clone().carry().carry().carry();
        let mut m = FieldElem::new();

        for _ in range(0, 3) {
            m.elem[0] = r.elem[0] - 0xffef;
            for j in range(1u, 25) {
                m.elem[j] = r.elem[j] - 0xffff - ((m.elem[j - 1] >> 16) & 1);
                m.elem[j - 1] &= 0xffff;
            }
            m.elem[25] = r.elem[25] - 0x3fff - ((m.elem[24] >> 16) & 1);
            m.elem[24] &= 0xffff;
            let b = (m.elem[25] >> 16) & 1;
            m.elem[25] &= 0xffff;
            utils::bytes_cswap(1 - b, r.elem, m.elem);
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
            r.elem[i] = n[2 * i] as i64 + (n[2 * i + 1] as i64 << 8);
        }
        for i in range(26u, l) {
            r.elem[i - 26] += (n[2 * i] as i64 +
                               (n[2 * i + 1] as i64 << 8)) * 68;
        }

        r.carry().carry()
    }

    pub fn parity_bit(&self) -> u8 {
        let t = self.pack();
        t[0] & 1
    }

    pub fn muli(&self, other: i16) -> FieldElem {
        let mut r = self.clone();

        for i in range(0, r.elem.len()) {
            r.elem[i] *= other as i64;
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
        for i in range(0, r.elem.len()) {
            r.elem[i] += other.elem[i];
        }
        r
    }
}

impl Sub<FieldElem, FieldElem> for FieldElem {
    fn sub(&self, other: &FieldElem) -> FieldElem {
        let mut r = self.clone();
        for i in range(0, r.elem.len()) {
            r.elem[i] -= other.elem[i];
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
                u += self.elem[j] * other.elem[i - j];
            }
            for j in range(i + 1, 26) {
                u += 68 * self.elem[j] * other.elem[i + 26 - j];
            }
            r.elem.as_mut_slice()[i] = u;
        }

        r.carry().carry()
    }
}

impl Drop for FieldElem {
    fn drop(&mut self) {
        self.cleanup();
    }
}

impl Clone for FieldElem {
    fn clone(&self) -> FieldElem {
        let mut n = FieldElem::new();
        let count = n.elem.len();
        utils::copy_slice_memory(n.elem.as_mut_slice(),
                                 self.elem.as_slice(), count);
        n
    }
}

impl Default for FieldElem {
    fn default() -> FieldElem {
        FieldElem::new()
    }
}

impl Show for FieldElem {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "{}", self.to_str_hex())
    }
}

impl PartialEq for FieldElem {
    fn eq(&self, other: &FieldElem) -> bool {
        self.pack() == other.pack()
    }
}

impl Eq for FieldElem {
}

impl Index<uint, i64> for FieldElem {
    fn index(&self, index: &uint) -> i64 {
        self.get_limb(*index)
    }
}
