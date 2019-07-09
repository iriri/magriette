#[macro_export]
macro_rules! pipe {
    ( $v:expr => $( $t:tt )=>+ ) => {
        {
            #[allow(unused_mut)]
            let mut v = $v;
            $(
                #[allow(unused_mut)]
                let mut v = $crate::pipe_match!($t, v);
            )*
            v
        }
    }
}

#[macro_export]
macro_rules! pipe_match {
    ( ref, $v:ident ) => {
        &$v
    };
    ( (ref), $v:ident ) => {
        &$v
    };
    ( (mut ref), $v:ident ) => {
        &mut $v
    };
    ( deref, $v:ident ) => {
        *$v
    };
    ( (deref), $v:ident ) => {
        *$v
    };
    ( {$f:expr}, $v:ident ) => {
        $f($v)
    };
    ( $f:ident, $v:ident ) => {
        $f($v)
    };
    ( ($f:ident), $v:ident ) => {
        $f($v)
    };
    ( ($f:ident($( $arg:expr ),*)), $v:ident ) => {
        $f($( $arg, )* $v)
    };
    ( ($f:ident($( $arg:expr, )*)), $v:ident ) => {
        $f($( $arg, )* $v)
    };
    ( ($f:ident?), $v:ident ) => {
        $f($v)?
    };
    ( ($f:ident($( $arg:expr ),*)?), $v:ident ) => {
        $f($( $arg, )* $v)?
    };
    ( ($f:ident($( $arg:expr, )*)?), $v:ident ) => {
        $f($( $arg, )* $v)?
    };
    ( (.$f:ident), $v:ident ) => {
        $v.$f()
    };
    ( (.$f:ident($( $arg:expr ),*)), $v:ident ) => {
        $v.$f($( $arg ),*)
    };
    ( (.$f:ident($( $arg:expr, )*)), $v:ident ) => {
        $v.$f($( $arg ),*)
    };
    ( (.$f:ident?), $v:ident ) => {
        $v.$f()?
    };
    ( (.$f:ident($( $arg:expr ),*)?), $v:ident ) => {
        $v.$f($( $arg ),*)?
    };
    ( (.$f:ident($( $arg:expr, )*)?), $v:ident ) => {
        $v.$f($( $arg ),*)?
    };
    ( [$i:expr], $v:ident ) => {
        $v[$i]
    };
    ( [.$i:tt], $v:ident ) => {
        $v.$i
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_ref() {
        let incr = |n: &u32| n + 1;
        fn incr_mut(n: &mut u32) -> &u32 {
            *n += 1;
            n
        }
        assert_eq!(2, pipe!(1 => ref => incr));
        assert_eq!(2, pipe!(1 => (mut ref) => incr_mut => deref));
        assert_eq!(2, pipe!(1 => (mut ref) => (incr_mut) => (ref) => (deref) => deref));
    }

    #[test]
    fn test_closure() {
        assert_eq!(2, pipe!(1 => {|n| n + 1}));
        assert_eq!(
            3,
            pipe!(1 => {|n| {
                let n = n + 1;
                n + 1
            }})
        );
    }

    #[test]
    fn test_fn() {
        let incr = |a| a + 1;
        let add2 = |a, b| a + b;
        let add3 = |a, b, c| a + b + c;
        assert_eq!(2, pipe!(1 => incr));
        assert_eq!(2, pipe!(1 => (add2(1))));
        assert_eq!(3, pipe!(1 => (add2(1,)) => (incr)));
        assert_eq!(4, pipe!(1 => (add3(0, 2)) => (incr())));
        assert_eq!(5, pipe!(1 => incr => (add3(1, 2,))));
    }

    #[test]
    fn test_method() {
        #[derive(Debug, PartialEq, Eq)]
        struct U32(u32);
        impl U32 {
            fn incr(self) -> U32 {
                U32(self.0 + 1)
            }

            fn add2(self, b: u32) -> U32 {
                U32(self.0 + b)
            }

            fn add3(self, b: u32, c: u32) -> U32 {
                U32(self.0 + b + c)
            }
        }

        assert_eq!(U32(2), pipe!(U32(1) => (.incr)));
        assert_eq!(U32(2), pipe!(U32(1) => (.add2(1))));
        assert_eq!(U32(3), pipe!(U32(1) => (.add2(1,)) => (.incr())));
        assert_eq!(U32(4), pipe!(U32(1) => (.add3(0, 2)) => (.incr())));
        assert_eq!(U32(5), pipe!(U32(1) => (.incr) => (.add3(1, 2,))));
    }

    #[test]
    fn test_index() {
        let a = [0, 1, 2];
        let i = 1;
        assert_eq!(0, pipe!(&a => [0]));
        assert_eq!(1, pipe!(&a => [i]));
        assert_eq!(2, pipe!(&a => [(|| 1 + 1)()]));
    }

    #[test]
    fn test_access() {
        struct Foo(u32, u32);
        struct Bar {
            _a: u32,
            b: u32,
        }
        let a = (0, 1);
        let b = Foo(2, 3);
        let c = Bar { _a: 4, b: 5 };
        assert_eq!(1, pipe!(&a => [.1]));
        assert_eq!(3, pipe!(&b => [.1]));
        assert_eq!(5, pipe!(&c => [.b]));
    }
}
