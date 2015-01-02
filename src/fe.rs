//! A Curve41417 field element representation
use rustc_serialize::hex::ToHex;
use std::default::Default;
use std::fmt::{Show, Formatter, Result};

use tars::{ProtBuf, ProtBuf8};

use common::{mod, BYTES_SIZE};


const FE_SIZE: uint = 26;

const ONE: [i64; FE_SIZE] = [
    1, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0
];


pub struct FieldElem {
    elem: ProtBuf<i64>
}

impl FieldElem {
    pub fn new() -> FieldElem {
        FieldElem::zero()
    }

    pub fn zero() -> FieldElem {
        FieldElem {
            elem: ProtBuf::new_zero(FE_SIZE)
        }
    }

    pub fn one() -> FieldElem {
        FieldElem {
            elem: ProtBuf::from_slice(ONE[])
        }
    }

    // Return a reference to the limb at index `index`; otherwise
    // return `None` if `index` is out of bounds.
    #[allow(dead_code)]
    pub fn get(&self, index: uint) -> Option<&i64> {
        self.elem.get(index)
    }

    // Return a mutable reference to the limb at index `index`; otherwise
    // return `None` if `index` is out of bounds.
    #[allow(dead_code)]
    pub fn get_mut(&mut self, index: uint) -> Option<&mut i64> {
        self.elem.get_mut(index)
    }

    pub fn unpack(bytes: &[u8]) -> Option<FieldElem> {
        if bytes.len() != BYTES_SIZE {
            return None;
        }

        let mut n = FieldElem::new();
        for i in range(0u, FE_SIZE) {
            n[i] = bytes[2 * i] as i64 + (bytes[2 * i + 1] as i64 << 8);
        }
        n[25] &= 0x3fff; // mask top 2 bits
        Some(n)
    }

    pub fn pack(&self) -> ProtBuf8 {
        let mut t = self.clone();
        t.reduce();

        let mut r = ProtBuf::new_zero(BYTES_SIZE);

        for i in range(0u, FE_SIZE) {
            r[2 * i] = (t[i] & 0xff) as u8;
            r[2 * i + 1] = (t[i] >> 8) as u8;
        }
        r
    }

    pub fn len(&self) -> uint {
        self.elem.len()
    }

    pub fn cswap(&mut self, cond: i64, other: &mut FieldElem) {
        common::bytes_cswap::<i64>(cond,
                                   self.elem.as_mut_slice(),
                                   other.elem.as_mut_slice());
    }

    pub fn carry(&mut self) {
        let mut c: i64;

        for i in range(0u, self.len()) {
            self[i] += 1_i64 << 16;
            c = self[i] >> 16;
            self[(i + 1) * ((i < 25) as uint)] += c - 1 + 67 * (c - 1) *
                ((i == 25) as i64);
            self[i] -= c << 16;
        }
    }

    // Fully reduce n mod 2^414 - 17
    pub fn reduce(&mut self) {
        self.carry();
        self.carry();
        self.carry();
        let mut m = FieldElem::new();

        for _ in range(0u, 3) {
            m[0] = self[0] - 0xffef;
            for j in range(1u, 25) {
                m[j] = self[j] - 0xffff - ((m[j - 1] >> 16) & 1);
                m[j - 1] &= 0xffff;
            }
            m[25] = self[25] - 0x3fff - ((m[24] >> 16) & 1);
            m[24] &= 0xffff;
            let b = (m[25] >> 16) & 1;
            m[25] &= 0xffff;
            self.cswap(1 - b, &mut m);
        }
    }

    // Reduce n mod 2^416 - 68 and put limbs between [0, 2^16-1] through carry.
    // Requirement: 52 < n.len() <= 104
    pub fn reduce_weak_from_bytes(n: &[u8]) -> Option<FieldElem> {
        if n.len() < BYTES_SIZE || n.len() > (BYTES_SIZE << 1) ||
           n.len() % 2 == 1 {
            return None;
        }

        let mut r = FieldElem::new();

        for i in range(0u, FE_SIZE) {
            r[i] = (*n)[2 * i] as i64 + ((*n)[2 * i + 1] as i64 << 8);
        }
        for i in range(FE_SIZE, n.len() >> 1) {
            r[i - 26] += ((*n)[2 * i] as i64 +
                          ((*n)[2 * i + 1] as i64 << 8)) * 68;
        }

        r.carry();
        r.carry();
        Some(r)
    }

    pub fn parity_bit(&self) -> u8 {
        let t = self.pack();
        t[0] & 1
    }

    #[allow(dead_code)]
    pub fn muli(&self, other: i16) -> FieldElem {
        let mut r = self.clone();

        for i in range(0u, r.len()) {
            r[i] *= other as i64;
        }

        r.carry();
        r.carry();
        r
    }

    pub fn square(&self) -> FieldElem {
        self.mul(self)
    }

    pub fn inv(&self) -> FieldElem {
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
    pub fn pow4139(&self) -> FieldElem {
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
    pub fn pow4125(&self) -> FieldElem {
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
    pub fn pow4124(&self) -> FieldElem {
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

impl Clone for FieldElem {
    fn clone(&self) -> FieldElem {
        FieldElem {
            elem: self.elem.clone()
        }
    }
}

impl Index<uint, i64> for FieldElem {
    fn index(&self, index: &uint) -> &i64 {
        &self.elem[*index]
    }
}

impl IndexMut<uint, i64> for FieldElem {
    fn index_mut(&mut self, index: &uint) -> &mut i64 {
        &mut self.elem[*index]
    }
}

fn add(a: &mut FieldElem, b: &FieldElem) {
    for i in range(0u, a.len()) {
        a[i] += b[i];
    }
}

impl<'a, 'b> Add<&'a FieldElem, FieldElem> for &'b FieldElem {
    fn add(self, other: &FieldElem) -> FieldElem {
        let mut r = self.clone();
        add(&mut r, other);
        r
    }
}

impl<'a> Add<&'a FieldElem, FieldElem> for FieldElem {
    // Add inplace
    fn add(mut self, other: &FieldElem) -> FieldElem {
        add(&mut self, other);
        self
    }
}

fn sub(a: &mut FieldElem, b: &FieldElem) {
    for i in range(0u, a.len()) {
        a[i] -= b[i];
    }
}

impl<'a, 'b> Sub<&'a FieldElem, FieldElem> for &'b FieldElem {
    fn sub(self, other: &FieldElem) -> FieldElem {
        let mut r = self.clone();
        sub(&mut r, other);
        r
    }
}

impl<'a> Sub<&'a FieldElem, FieldElem> for FieldElem {
    // Sub inplace
    fn sub(mut self, other: &FieldElem) -> FieldElem {
        sub(&mut self, other);
        self
    }
}

impl<'a> Neg<FieldElem> for &'a FieldElem {
    fn neg(self) -> FieldElem {
        &FieldElem::zero() - self
    }
}

impl Neg<FieldElem> for FieldElem {
    fn neg(self) -> FieldElem {
        &FieldElem::zero() - &self
    }
}

impl<'a, 'b> Mul<&'a FieldElem, FieldElem> for &'b FieldElem {
    fn mul(self, other: &FieldElem) -> FieldElem {
        let mut u: i64;
        let mut r = FieldElem::new();

        for i in range(0u, FE_SIZE) {
            u = 0;
            for j in range(0u, i + 1) {
                u += self[j] * other[i - j];
            }
            for j in range(i + 1, FE_SIZE) {
                u += 68 * self[j] * other[i + FE_SIZE - j];
            }
            r[i] = u;
        }

        r.carry();
        r.carry();
        r
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
