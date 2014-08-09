// A Curve41417 field element representation.
use serialize::hex::ToHex;
use std::default::Default;
use std::fmt::{Show, Formatter, Result};

use bytes::{B416, Bytes, Uniformity};
use sbuf::{Allocator, SBuf};
use utils;


static FE_SIZE: uint = 26;

static ONE: [i64, ..FE_SIZE] = [
    1, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0
];


pub struct FieldElem<A> {
    elem: SBuf<A, i64>
}

impl<A: Allocator> FieldElem<A> {
    pub fn new() -> FieldElem<A> {
        FieldElem::zero()
    }

    pub fn zero() -> FieldElem<A> {
        FieldElem {
            elem: SBuf::new_zero(FE_SIZE)
        }
    }

    pub fn one() -> FieldElem<A> {
        FieldElem {
            elem: SBuf::from_slice(ONE.as_slice())
        }
    }

    // Return a reference to the limb at index `index`. Fails if
    // `index` is out of bounds.
    pub fn get(&self, index: uint) -> &i64 {
        self.elem.get(index)
    }

    // Return a mutable reference to the limb at index `index`. Fails
    // if `index` is out of bounds.
    pub fn get_mut(&mut self, index: uint) -> &mut i64 {
        self.elem.get_mut(index)
    }

    pub fn unpack(bytes: &B416<A>) -> FieldElem<A> {
        let mut n: FieldElem<A> = FieldElem::new();

        for i in range(0u, 26) {
            n[i] = bytes[2 * i] as i64 + (bytes[2 * i + 1] as i64 << 8);
        }
        n[25] &= 0x3fff; // mask top 2 bits
        n
    }

    pub fn pack(&self) -> B416<A> {
        let t = self.clone().reduce();
        let mut r: B416<A> = Bytes::new_zero();

        for i in range(0u, FE_SIZE) {
            r[2 * i] = (t[i] & 0xff) as u8;
            r[2 * i + 1] = (t[i] >> 8) as u8;
        }
        r
    }

    pub fn cswap(&mut self, cond: i64, other: &mut FieldElem<A>) {
        utils::bytes_cswap::<i64>(cond,
                                  self.elem.as_mut_slice(),
                                  other.elem.as_mut_slice());
    }

    pub fn carry(&self) -> FieldElem<A> {
        let mut r = self.clone();
        let mut c: i64;

        for i in range(0u, r.len()) {
            r[i] += 1_i64 << 16;
            c = r[i] >> 16;
            r[(i + 1) * ((i < 25) as uint)] += c - 1 + 67 * (c - 1) *
                ((i == 25) as i64);
            r[i] -= c << 16;
        }
        r
    }

    // Fully reduce n mod 2^414 - 17
    pub fn reduce(&self) -> FieldElem<A> {
        let mut r = self.clone().carry().carry().carry();
        let mut m: FieldElem<A> = FieldElem::new();

        for _ in range(0u, 3) {
            m[0] = r[0] - 0xffef;
            for j in range(1u, 25) {
                m[j] = r[j] - 0xffff - ((m[j - 1] >> 16) & 1);
                m[j - 1] &= 0xffff;
            }
            m[25] = r[25] - 0x3fff - ((m[24] >> 16) & 1);
            m[24] &= 0xffff;
            let b = (m[25] >> 16) & 1;
            m[25] &= 0xffff;
            r.cswap(1 - b, &mut m);
        }
        r
    }

    // Reduce n mod 2^416 - 68 and put limbs between [0, 2^16-1] through carry.
    // Requirement: 52 < n.len() <= 104
    pub fn reduce_weak_from_bytes<T: Bytes + Uniformity>(n: &T)
                                                         -> FieldElem<A> {
        let l = n.as_bytes().len() / 2;
        assert!(l > 26 && l <= 52);

        let mut r: FieldElem<A> = FieldElem::new();

        for i in range(0u, 26) {
            r[i] = (*n)[2 * i] as i64 + ((*n)[2 * i + 1] as i64 << 8);
        }
        for i in range(26u, l) {
            r[i - 26] += ((*n)[2 * i] as i64 +
                          ((*n)[2 * i + 1] as i64 << 8)) * 68;
        }

        r.carry().carry()
    }

    pub fn parity_bit(&self) -> u8 {
        let t = self.pack();
        t[0] & 1
    }

    #[allow(dead_code)]
    pub fn muli(&self, other: i16) -> FieldElem<A> {
        let mut r = self.clone();

        for i in range(0u, r.len()) {
            r[i] *= other as i64;
        }

        r.carry().carry()
    }

    pub fn square(&self) -> FieldElem<A> {
        self.mul(self)
    }

    pub fn inv(&self) -> FieldElem<A> {
        let mut r = self.clone();

        for i in range(0u, 413).rev() {
            r = r.square();
            if i != 1 && i != 4 {
                r = r.mul(self);
            }
        }
        r
    }

    // Legendre symbol.
    // i ** ((P - 1) / 2) = i ** (2 ** 413 - 9)
    pub fn pow4139(&self) -> FieldElem<A> {
        let mut r = self.clone();

        for i in range(0u, 412).rev() {
            r = r.square();
            if i != 3 {
                r = r.mul(self);
            }
        }
        r
    }

    // i ** ((P - 3) / 4) = i ** (2 ** 412 - 5)
    pub fn pow4125(&self) -> FieldElem<A> {
        let mut r = self.clone();

        for i in range(0u, 411).rev() {
            r = r.square();
            if i != 2 {
                r = r.mul(self);
            }
        }
        r
    }

    // Principal square root for p = 3 mod 4.
    // i ** ((P + 1) / 4) = i ** (2 ** 412 - 4)
    pub fn pow4124(&self) -> FieldElem<A> {
        let mut r = self.clone();

        for i in range(0u, 411).rev() {
            r = r.square();
            if i != 0 && i != 1 {
                r = r.mul(self);
            }
        }
        r
    }
}

impl<A: Allocator> Clone for FieldElem<A> {
    fn clone(&self) -> FieldElem<A> {
        FieldElem {
            elem: self.elem.clone()
        }
    }
}

impl<A: Allocator> Index<uint, i64> for FieldElem<A> {
    fn index(&self, index: &uint) -> &i64 {
        self.get(*index)
    }
}

impl<A: Allocator> IndexMut<uint, i64> for FieldElem<A> {
    fn index_mut(&mut self, index: &uint) -> &mut i64 {
        self.get_mut(*index)
    }
}

impl<A: Allocator> Add<FieldElem<A>, FieldElem<A>> for FieldElem<A> {
    fn add(&self, other: &FieldElem<A>) -> FieldElem<A> {
        let mut r = self.clone();
        for i in range(0u, r.len()) {
            r[i] += other[i];
        }
        r
    }
}

impl<A: Allocator> Sub<FieldElem<A>, FieldElem<A>> for FieldElem<A> {
    fn sub(&self, other: &FieldElem<A>) -> FieldElem<A> {
        let mut r = self.clone();
        for i in range(0u, r.len()) {
            r[i] -= other[i];
        }
        r
    }
}

impl<A: Allocator> Neg<FieldElem<A>> for FieldElem<A> {
    fn neg(&self) -> FieldElem<A> {
        FieldElem::zero() - *self
    }
}

impl<A: Allocator> Mul<FieldElem<A>, FieldElem<A>> for FieldElem<A> {
    fn mul(&self, other: &FieldElem<A>) -> FieldElem<A> {
        let mut u: i64;
        let mut r: FieldElem<A> = FieldElem::new();

        for i in range(0u, 26) {
            u = 0;
            for j in range(0u, i + 1) {
                u += self[j] * other[i - j];
            }
            for j in range(i + 1, 26) {
                u += 68 * self[j] * other[i + 26 - j];
            }
            r[i] = u;
        }

        r.carry().carry()
    }
}

impl<A: Allocator> Default for FieldElem<A> {
    fn default() -> FieldElem<A> {
        FieldElem::new()
    }
}

impl<A: Allocator> Show for FieldElem<A> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        self.pack().fmt(f)
    }
}

impl<A: Allocator> ToHex for FieldElem<A> {
    fn to_hex(&self) -> String {
        self.pack().to_hex()
    }
}

impl<A: Allocator> PartialEq for FieldElem<A> {
    fn eq(&self, other: &FieldElem<A>) -> bool {
        self.pack() == other.pack()
    }
}

impl<A: Allocator> Eq for FieldElem<A> {
}

impl<A: Allocator> Collection for FieldElem<A> {
    fn len(&self) -> uint {
        self.elem.len()
    }
}
