#[macro_export]
macro_rules! forward_ref_op_binary {
    ($(#[$attr: meta])*
    impl $(<$($type_param: tt),*>)? $binary_imp: ident, $binary_method: ident
    for $t: ty, $u: ty, $v: ty
    $(where [$($preds: tt)+])? {
        $(type $type_id: ident = $type_value: ty;)*
    }) => {
        $(#[$attr])*
        impl$(<$($type_param),*>)? $binary_imp<$u> for &$t
            $(where $($preds)+)? {
            $(type $type_id = $type_value);*;
            #[inline]
            fn $binary_method(self, other: $u) -> $v {
                $binary_imp::$binary_method(self, &other)
            }
        }
        $(#[$attr])*
        impl$(<$($type_param),*>)? $binary_imp<&$u> for $t
            $(where $($preds)+)? {
            $(type $type_id = $type_value);*;
            #[inline]
            fn $binary_method(self, other: &$u) -> $v {
                $binary_imp::$binary_method(&self, other)
            }
        }
        $(#[$attr])*
        impl$(<$($type_param),*>)? $binary_imp<$u> for $t
            $(where $($preds)+)? {
            $(type $type_id = $type_value);*;
            #[inline]
            fn $binary_method(self, other: $u) -> $v {
                $binary_imp::$binary_method(&self, &other)
            }
        }
    };
    ($(#[$attr: meta])*
    impl $(<$($type_param: tt),*>)? $binary_imp: ident, $binary_method: ident
    for $t: ty, $u: ty, $v: ty
    $(where [$($preds: tt)+])?) => {
        forward_ref_op_binary! {
            $(#[$attr])*
            impl$(<$($ type_param),*>)? $binary_imp, $binary_method for $t, $u, $v
            $(where [$($preds)+])? {
                type Output = $v;
            }
        }
    };
}

// implements "T op= &U", "T op= U", "&T op U", "T op &U", "T op U"
// based on "&T op &U"
#[macro_export]
macro_rules! forward_ref_op_assign_and_binary {
    ($(#[$attr: meta])*
    impl $(<$($type_param: tt),*>)? $binary_imp: ident, $binary_method: ident,
    impl $assign_imp: ident, $assign_method: ident for $t: ty, $u: ty, $v: ty
    $(where [$($preds: tt)+])? $({
        $(type $type_id: ident = $type_value: ty;)*
    })?) => {
        $(#[$attr])*
        impl$(<$($type_param),*>)? $assign_imp<&$u> for $t
            $(where $($preds)+)? {
            #[inline]
            fn $assign_method(&mut self, rhs: &$u) {
                *self = $binary_imp::$binary_method(&*self, rhs);
            }
        }
        $(#[$attr])*
        impl$(<$($type_param),*>)? $assign_imp<$u> for $t
            $(where $($preds)+)? {
            #[inline]
            fn $assign_method(&mut self, rhs: $u) {
                $assign_imp::$assign_method(self, &rhs);
            }
        }
        forward_ref_op_binary! {
            $(#[$attr])*
            impl$(<$($ type_param),*>)? $binary_imp, $binary_method for $t, $u, $v
            $(where [$($preds)+])? $({
                $(type $type_id = $type_value;)*
            })?
        }
    }
}
