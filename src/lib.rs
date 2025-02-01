//! # Examples
//! ```
//! # use magriette::pipe;
//! #
//! fn dederef(x: &&u32) -> u32 {
//!    **x
//! }
//!
//! fn lol(xs: &[u32], ys: &[usize]) -> Option<u32> {
//!    // An even worse way of writing `Some(dederef(&xs.get(*ys.get(123)?)?))`
//!    pipe!(ys -> .get(123)? -> *xs.get? -> &dederef -> Some)
//! }
//! ```
#![no_std]

#[macro_export]
macro_rules! pipe {
   (@finish $x:expr, .await $($xs:tt)*) => {
      $crate::pipe!(@finish ($x).await, $($xs)*)
   };
   (@finish $x:expr, ? $($xs:tt)*) => {
      $crate::pipe!(@finish ($x)?, $($xs)*)
   };
   (@finish $x:expr, -> $($xs:tt)+) => {
      $crate::pipe!(@start $x, [], $($xs)+)
   };
   (@finish $x:expr, => $($xs:tt)+) => {
      $crate::pipe!(@start2 $x, [], [], $($xs)+)
   };
   (@finish $x:expr,) => {
      $x
   };
   (@call ($($x:expr),+), [$($f:tt)+], .$f1:ident $($xs:tt)*) => {
      $crate::pipe!(@call ($($x),+), [$($f)+.$f1], $($xs)*)
   };
   (@call ($($x:expr),+), [$($f:tt)+], ::$f1:ident $($xs:tt)*) => {
      $crate::pipe!(@call ($($x),+), [$($f)+::$f1], $($xs)*)
   };
   (@call ($($x:expr),+), [$($f:tt)+], ::<$($t:ty),+> $($xs:tt)*) => {
      $crate::pipe!(@call ($($x),+), [$($f)+::<$($t)+>], $($xs)*)
   };
   (@call ($($x:expr),+), [$($f:tt)+], ! $($xs:tt)*) => {
      $crate::pipe!(@call ($($x),+), [$($f)+!], $($xs)*)
   };
   (@call ($($x:expr),+), [$($f:tt)+], ($($y:expr),+) $($xs:tt)*) => {
      $crate::pipe!(@call ($($y,)+ $($x),+), [$($f)+], $($xs)*)
   };
   (@call ($($x:expr),+), [$($f:tt)+], $($xs:tt)*) => {
      $crate::pipe!(@finish $($f)+($($x),+), $($xs)*)
   };
   (@method $x:expr, [$($f:tt)+]($($y:expr),*), [$($z:expr),*], ::<$($t:ty),+> $($xs:tt)*) => {
      $crate::pipe!(@method $x, [$($f)+::<$($t),+>]($($y,)*), [$($z),*], $($xs)*)
   };
   (@method $x:expr, [$($f:tt)+]($($y:expr),*), [$($z:expr),*], ($($zz:expr),+) $($xs:tt)*) => {
      $crate::pipe!(@method $x, [$($f)+]($($y,)* $($zz),+), [$($z),*], $($xs)*)
   };
   (@method $x:expr, [$($f:tt)+]($($y:expr),*), [$($z:expr),*], $($xs:tt)*) => {
      $crate::pipe!(@finish ($x).$($f)+($($y,)*$($z),*), $($xs)*)
   };
   (@start $x:expr, [$($u:tt)*], &mut $($xs:tt)*) => {
      $crate::pipe!(@start $x, [$($u)* &mut], $($xs)*)
   };
   (@start $x:expr, [$($u:tt)*], && $($xs:tt)*) => {
      $crate::pipe!(@start $x, [$($u)* &&], $($xs)*)
   };
   (@start $x:expr, [$($u:tt)*], & $($xs:tt)*) => {
      $crate::pipe!(@start $x, [$($u)* &], $($xs)*)
   };
   (@start $x:expr, [$($u:tt)*], * $($xs:tt)*) => {
      $crate::pipe!(@start $x, [$($u)* *], $($xs)*)
   };
   (@start $x:expr, [$($u:tt)*], await $($xs:tt)*) => {
      $crate::pipe!(@start ($x).await, [$($u)*], $($xs)*)
   };
   (@start $x:expr, [$($u:tt)*], ? $($xs:tt)*) => {
      $crate::pipe!(@start ($x)?, [$($u)*], $($xs)*)
   };
   (@start $x:expr, [$($u:tt)*], -> $($xs:tt)+) => {
      $crate::pipe!(@start $($u)*($x), [], $($xs)+)
   };
   (@start $x:expr, [$($u:tt)*], => $($xs:tt)+) => {
      $crate::pipe!(@start2 $($u)*($x), [], [], $($xs)+)
   };
   (@start $x:expr, [$($u:tt)*], match $c:tt $($xs:tt)*) => {
      $crate::pipe!(@finish match $($u)*($x) $c, $($xs)*)
   };
   (@start $x:expr, [$($u:tt)*], if $t:block else $f:block $($xs:tt)*) => {
      $crate::pipe!(@finish if $($u)*($x) $t else $f, $($xs)*)
   };
   (@start $x:expr, [$($u:tt)*], $f:ident $($xs:tt)*) => {
      $crate::pipe!(@call ($($u)*($x)), [$f], $($xs)*)
   };
   (@start $x:expr, [$($u:tt)*], .$f:ident $($xs:tt)*) => {
      $crate::pipe!(@method $($u)*($x), [$f](), [], $($xs)*)
   };
   (@start $x:expr, [$($u:tt)*], [.$($p:tt)+] $($xs:tt)*) => {
      $crate::pipe!(@finish ($($u)*($x)).$($p)+, $($xs)*)
   };
   (@start $x:expr, [$($u:tt)*], [$i:expr] $($xs:tt)*) => {
      $crate::pipe!(@finish ($($u)*($x))[$i], $($xs)*)
   };
   (@start $x:expr, [$($u:tt)*], _) => {{
      let _ = $($u)*($x);
   }};
   (@start $x:expr, [$($u:tt)*], |$y:pat_param| $e:block -> $($xs:tt)*) => {
      $crate::pipe!(@start (|$y| $e)($($u)*($x)), [], $($xs)*)
   };
   (@start $x:expr, [$($u:tt)*], |$y:pat_param| $e:block => $($xs:tt)*) => {
      $crate::pipe!(@start2 (|$y| $e)($($u)*($x)), [], [], $($xs)*)
   };
   (@start $x:expr, [$($u:tt)*], |$y:pat_param| $e:block) => {
      (|$y| $e)($($u)*($x))
   };
   (@start $x:expr, [$($u:tt)*],) => {
      $($u)*($x)
   };
   (@start2 $x:expr, [$($u:tt)*], [$($s:tt)*], &mut $($xs:tt)*) => {
      $crate::pipe!(@start2 $x, [$($u)* &mut], [$($s)*], $($xs)*)
   };
   (@start2 $x:expr, [$($u:tt)*], [$($s:tt)*], && $($xs:tt)*) => {
      $crate::pipe!(@start2 $x, [$($u)* &&], [$($s)*], $($xs)*)
   };
   (@start2 $x:expr, [$($u:tt)*], [$($s:tt)*], & $($xs:tt)*) => {
      $crate::pipe!(@start2 $x, [$($u)* &], [$($s)*], $($xs)*)
   };
   (@start2 $x:expr, [$($u:tt)*], [$($s:tt)*], * $($xs:tt)*) => {
      $crate::pipe!(@start2 $x, [$($u)* *], [$($s)*], $($xs)*)
   };
   (@start2 $x:expr, [$($u:tt)*], [$($s:tt)*], await $($xs:tt)*) => {
      $crate::pipe!(@start2 $x, [$($u)*], [$($s)*.await], $($xs)*)
   };
   (@start2 $x:expr, [$($u:tt)*], [$($s:tt)*], ? $($xs:tt)*) => {
      $crate::pipe!(@start2 $x, [$($u)*], [$($s)*?], $($xs)*)
   };
   (@start2 $x:expr, [$($u:tt)*], [$($s:tt)*], -> $($xs:tt)+) => {{
      #[allow(unused_mut)]
      let mut x = $x;
      $crate::pipe!(@start ($($u)*x.0$($s)*, $($u)*x.1$($s)*), [], $($xs)+)
   }};
   (@start2 $x:expr, [$($u:tt)*], [$($s:tt)*], => $($xs:tt)+) => {{
      #[allow(unused_mut)]
      let mut x = $x;
      $crate::pipe!(@start2 ($($u)*x.0$($s)*, $($u)*x.1$($s)*), [], [], $($xs)+)
   }};
   (@start2 $x:expr, [$($u:tt)*], [$($s:tt)*], match $c:tt $($xs:tt)*) => {{
      #[allow(unused_mut)]
      let mut x = $x;
      $crate::pipe!(@finish match ($($u)*x.0$($s)*, $($u)*x.1$($s)*) $c, $($xs)*)
   }};
   (@start2 $x:expr, [$($u:tt)*], [$($s:tt)*], $f:ident $($xs:tt)*) => {{
      #[allow(unused_mut)]
      let mut x = $x;
      $crate::pipe!(@call ($($u)*x.0$($s)*, $($u)*x.1$($s)*), [$f], $($xs)*)
   }};
   (
      @start2 $x:expr,
      [$($u:tt)*],
      [$($s:tt)*],
      |$y:pat_param, $z:pat_param| $e:block -> $($xs:tt)*) =>
   {{
      #[allow(unused_mut)]
      let mut x = $x;
      $crate::pipe!(@start (|$y, $z| $e)($($u)*x.0$($s)*, $($u)*x.1$($s)*), [], $($xs)*)
   }};
   (
      @start2 $x:expr,
      [$($u:tt)*],
      [$($s:tt)*],
      |$y:pat_param, $z:pat_param| $e:block => $($xs:tt)*) =>
   {{
      #[allow(unused_mut)]
      let mut x = $x;
      $crate::pipe!(@start2 (|$y, $z| $e)($($u)*x.0$($s)*, $($u)*x.1$($s)*), [], [], $($xs)*)
   }};
   (@start2 $x:expr, [$($u:tt)*], [$($s:tt)*], |$y:pat_param, $z:pat_param| $e:block) => {{
      #[allow(unused_mut)]
      let mut x = $x;
      (|$y, $z| $e)($($u)*x.0$($s)*, $($u)*x.1$($s)*)
   }};
   (@start2 $x:expr, [$($u:tt)*], [$($s:tt)*],) => {{
      #[allow(unused_mut)]
      let mut x = $x;
      ($($u)*x.0$($s)*, $($u)*x.1$($s)*)
   }};
   (@init [$($x:tt)+], -> $($xs:tt)+) => {
      $crate::pipe!(@start $($x)+, [], $($xs)+)
   };
   (@init [$($x:tt)+], => $($xs:tt)+) => {
      $crate::pipe!(@start2 $($x)+, [], [], $($xs)+)
   };
   (@init [$($x:tt)+], $x1:tt $($xs:tt)*) => {
      $crate::pipe!(@init [$($x)+$x1], $($xs)*)
   };
   (@init [$x:expr],) => {
      $x
   };
   (@$($xs:tt)*) => {
      compile_error!("Failed to match rule")
   };
   ($x:tt $($xs:tt)*) => {
      $crate::pipe!(@init [$x], $($xs)*)
   };
}

#[cfg(test)]
mod tests {
   mod foo {
      pub fn ident<T>(x: T) -> T {
         x
      }

      pub fn second<T>(_: T, x: T) -> T {
         x
      }

      pub fn third<T>(_: T, _: T, x: T) -> T {
         x
      }
   }

   mod bar {
      pub fn wrap<T>(x: T) -> Option<T> {
         Some(x)
      }

      pub fn wrap2<T>(x: T, y: T) -> (Option<T>, Option<T>) {
         (Some(x), Some(y))
      }
   }

   use bar::*;
   use foo::*;

   #[test]
   fn r#ref() {
      assert_eq!(&0, pipe!(0 -> & -> ident));
      assert_eq!(&0, pipe!(0 -> &ident));
      assert_eq!(&mut 0, pipe!(0 -> &mut -> foo::ident));
      assert_eq!(&mut 0, pipe!(0 -> &mut foo::ident::<&mut u32>));
      assert_eq!(0, pipe!(0 -> & -> second(&1) -> *));
      assert_eq!(0, pipe!(0 -> &&second(&&1) -> **));
      assert_eq!(0, pipe!(0 -> &mut -> foo::third(&mut 1, &mut 2) -> *));
      assert_eq!(0, pipe!(0 -> &mut foo::third(&mut 1)(&mut 2) -> *));

      assert_eq!(1, pipe!((0, 1) => & => second -> *));
      assert_eq!(1, pipe!((0, 1) => &second -> *));
      assert_eq!(1, pipe!((0, 1) => &mut  => second -> *));
      assert_eq!(1, pipe!((0, 1) => &mut second -> *));
      assert_eq!(1, pipe!((0, 1) => && => second -> **));
      assert_eq!(1, pipe!((0, 1) => &&second -> **));
      assert_eq!(1, pipe!((0, 1) => &third(&2) -> *));
   }

   #[test]
   fn r#try() {
      fn inner() -> Option<()> {
         assert_eq!(0, pipe!(Some(0) -> ? -> ident));
         assert_eq!(0, pipe!(Some(0) -> ?foo::ident));
         assert_eq!(0, pipe!(0 -> wrap -> ?));
         assert_eq!(0, pipe!(0 -> wrap? -> ident::<_>));
         assert_eq!(0, pipe!(Some(0) -> bar::wrap -> ? -> ?));
         assert_eq!(0, pipe!(Some(0) -> bar::wrap -> ??));
         assert_eq!(0, pipe!(Some(0) -> bar::wrap? -> ?));
         assert_eq!(0, pipe!(Some(0) -> bar::wrap??));
         assert_eq!((0, 1), pipe!((0, 1) => wrap2 => ?));
         assert_eq!((0, 1), pipe!((0, 1) => bar::wrap2 => ?));
         assert_eq!((0, 1), pipe!((Some(0), Some(1)) => ?wrap2 => ?));
         assert_eq!((0, 1), pipe!((Some(0), Some(1)) => ?bar::wrap2 => ?));
         pipe!(None::<()> -> bar::wrap??);
         unreachable!();
      }
      inner();
   }

   #[test]
   fn method() {
      #[derive(Debug, PartialEq, Eq)]
      struct U32(u32);

      impl U32 {
         fn incr(self) -> U32 {
            U32(self.0 + 1)
         }

         fn add2(&self, b: u32) -> U32 {
            U32(self.0 + b)
         }

         fn add3(&mut self, b: u32, c: u32) -> U32 {
            U32(self.0 + b + c)
         }

         fn add4(&mut self, b: u32, c: u32, d: u32) -> U32 {
            U32(self.0 + b + c + d)
         }

         fn add_assign(&mut self, b: u32) -> U32 {
            self.0 += b;
            U32(self.0)
         }

         fn konst<T>(&self, x: T) -> T {
            x
         }
      }

      let mut x = U32(0);
      assert_eq!(U32(1), pipe!(U32(0) -> .incr));
      assert_eq!(U32(1), pipe!(U32(0) -> .add2(1)));
      assert_eq!(U32(2), pipe!(U32(0) -> &.add2(1) -> .incr));
      assert_eq!(U32(3), pipe!(U32(0) -> .add3(1, 2)));
      assert_eq!(U32(4), pipe!(U32(0) -> &mut .add3(1, 2) -> .incr));
      assert_eq!(U32(5), pipe!(5 -> x.add_assign));
      assert_eq!(U32(6), pipe!(0 -> x.add3(1)));
      assert_eq!(U32(7), pipe!(U32(0) -> .konst::<_>(U32(7))));
      assert_eq!(U32(8), pipe!((1, 2) => x.add3));
      assert_eq!(U32(9), pipe!((0, 1) => x.add4(3)));
   }

   #[test]
   fn index() {
      let xs = [0, 1, 2];
      assert_eq!(0, pipe!(xs -> [0]));
      assert_eq!(1, pipe!(&xs -> [1]));
      assert_eq!(2, pipe!(xs -> &[1 + 1]));
      assert_eq!(3, pipe!(xs -> &[2] -> |x| { x + 1 }));
   }

   #[test]
   fn access() {
      struct Foo(u32, u32);

      struct Bar {
         a: u32,
         b: Foo,
      }

      let x = (0, 1);
      let y = Foo(2, 3);
      let z = Bar { a: 4, b: Foo(5, 6) };
      assert_eq!(0, pipe!(x -> [.0]));
      assert_eq!(1, pipe!(x -> &[.1]));
      assert_eq!(2, pipe!(&y -> [.0]));
      assert_eq!(3, pipe!(&y -> [.1]));
      assert_eq!(4, pipe!(&z -> [.a]));
      assert_eq!(5, pipe!(z -> &[.b] -> [.0]));
      assert_eq!(6, pipe!(&z -> &[.b.1]));
   }

   #[test]
   fn sink() {
      assert_eq!((), pipe!(0 -> _));
   }

   #[test]
   fn r#match() {
      assert_eq!(0, pipe!(false -> match { false => 0, true => 1}));
      assert_eq!(
         1,
         pipe!(false
            -> match { false => true, true => false}
            -> *&match { false => 0, true => 1}),
      );
      assert_eq!((1, 2), pipe!((0, 1) => &match { (x, y) => (*x + 1, *y + 1) }));
   }

   #[test]
   fn r#if() {
      assert_eq!(0, pipe!(false -> if { 1 } else { 0 }));
      assert_eq!(
         1,
         pipe!(false
            -> if { false } else { true }
            -> *&if { 1 } else { 0 }),
      );
   }

   #[test]
   fn closure() {
      assert_eq!(1, pipe!(0 -> |x| { x + 1 }));
      assert_eq!(
         2,
         pipe!(0 -> |x| {
             let x = x + 1;
             x + 1
         }),
      );
      assert_eq!(
         3,
         pipe!(0
            -> |x| {
                let x = x + 1;
                x + 1
            }
            -> |x| { x + 1 }),
      );
      assert_eq!(4, pipe!((0, 1) -> |(x, y)| { (x + 1, y + 1) } => |x, y| { x + y + 1 }));
   }

   #[test]
   fn combo() {
      struct Foo(Option<u32>);

      impl Foo {
         fn wrap(&self) -> Option<Option<u32>> {
            Some(self.0)
         }
      }

      fn inner() -> Option<()> {
         assert_eq!(0, pipe!(Some(0) -> *&?bar::wrap?));
         assert_eq!(0, pipe!(Some(Some(Foo(Some(0)))) -> ?&&&*&&&*&?.wrap??));
         Some(())
      }
      inner();
   }

   #[test]
   fn pointless() {
      assert_eq!(0, pipe!(0 -> pipe! -> pipe!));
   }
}
