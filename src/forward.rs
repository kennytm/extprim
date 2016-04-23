macro_rules! forward_symmetric {
    (
        $(#[$cattr:meta])*
        impl $tn:ident($name:ident, $cname:ident, $wname:ident, $oname:ident) for $target:ty
    ) => {
        forward_symmetric!(
            $(#[$cattr])*
            impl $tn<$target>($name, $cname, $wname, $oname) for $target
        );
    };
    (
        $(#[$cattr:meta])*
        impl $tn:ident<$arg:ty>($name:ident, $cname:ident, $wname:ident, $oname:ident) for $target:ty
    ) => {
        forward_impl! {
            $(#[$cattr])*
            impl $tn<
                $arg;
                $arg { y => y };
                Wrapping<$arg> { x => x.0 }
            > ($name, $cname, $wname, $oname) for $target, "arithmetic operation overflowed"
        }
    }
}

macro_rules! forward_shift {
    (
        $(#[$cattr:meta])*
        impl $tn:ident($name:ident, $cname:ident, $wname:ident, $oname:ident) for $target:ty
    ) => {
        forward_impl! {
            $(#[$cattr])*
            impl $tn<
                u32;
                u8|u16|u32|u64|usize|i8|i16|i32|i64|isize { y => y.to_u32().unwrap_or_else(|| panic!("shift operation overflowed")) };
                u32 { x => x }
            > ($name, $cname, $wname, $oname) for $target, "shift operation overflowed"
        }
    }
}

macro_rules! forward_assign {
    ($tn:ident($name:ident, $fwd:ident) for $target:ty) => {
        forward_assign!($tn<$target>($name, $fwd) for $target);
    };
    ($tn:ident<$($targ:ty)|+>($name:ident, $fwd:ident) for $target:ty) => {
        $(impl $tn<$targ> for $target {
            fn $name(&mut self, other: $targ) {
                *self = self.$fwd(other);
            }
        })+
    }
}

macro_rules! forward_impl {
    (
        $(#[$cattr:meta])*
        impl $tn:ident<
            $arg:ty;
            $($targ:ty)|+ { $t:pat => $uncheck_cast:expr };
            $wrarg:ty { $u:pat => $unwrap:expr }
        > ($name:ident, $cname:ident, $wname:ident, $oname:ident) for $target:ty,
        $emsg:expr
    ) => {
        impl $target {
            $(#[$cattr])*
            pub fn $cname(self, other: $arg) -> Option<$target> {
                match self.$oname(other) {
                    (v, false) => Some(v),
                    (_, true) => None,
                }
            }
        }

        $(impl $tn<$targ> for $target {
            type Output = Self;
            #[cfg(debug_assertions)]
            #[allow(unused_comparisons, overflowing_literals)]
            fn $name(self, other: $targ) -> Self {
                let other = match other {
                    $t => $uncheck_cast,
                };
                self.$cname(other).unwrap_or_else(|| panic!($emsg))
            }
            #[cfg(not(debug_assertions))]
            fn $name(self, other: $targ) -> Self {
                self.$wname(match other { $t => $uncheck_cast })
            }
        })+

        impl $tn<$wrarg> for Wrapping<$target> {
            type Output = Self;
            fn $name(self, other: $wrarg) -> Self {
                match other {
                    $u => Wrapping((self.0).$wname($unwrap))
                }
            }
        }
    }
}

