/// # Examples
/// ```
/// use magriette::pipe;
///
/// fn dederef(x: &&u32) -> u32 {
///    **x
/// }
///
/// fn lol(xs: &[u32], ys: &[usize]) -> Option<u32> {
///    // An even worse way of writing `Some(dederef(&xs.get(*ys.get(123)?)?))`
///    pipe!(ys -> .get(123)? -> *xs.get? -> &dederef -> Some)
/// }
/// ```
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
   (@finish $x:expr,) => {
      $x
   };
   (@call ($x:expr), [$($f:tt)+], ::$f1:ident $($xs:tt)*) => {
      $crate::pipe!(@call ($x), [$($f)+::$f1], $($xs)*)
   };
   (@call ($x:expr), [$($f:tt)+], ::<$($t:ty),+> $($xs:tt)*) => {
      $crate::pipe!(@call ($x), [$($f)+::<$($t)+>], $($xs)*)
   };
   (@call ($($x:expr),+), [$($f:tt)+], ($($y:expr),+) $($xs:tt)*) => {
      $crate::pipe!(@call ($($y,)+ $($x),+), [$($f)+], $($xs)*)
   };
   (@call ($($x:expr),+), [$($f:tt)+], $($xs:tt)*) => {
      $crate::pipe!(@finish $($f)+($($x),+), $($xs)*)
   };
   (@method $x:expr, [$($f:tt)+]($($y:expr),*), $($z:expr)?, ::<$($t:ty),+> $($xs:tt)*) => {
      $crate::pipe!(@method $x, [$($f)+::<$($t),+>]($($y,)*), $($z)?, $($xs)*)
   };
   (@method $x:expr, [$($f:tt)+]($($y:expr),*), $($z:expr)?, ($($zz:expr),+) $($xs:tt)*) => {
      $crate::pipe!(@method $x, [$($f)+]($($y,)* $($zz),+), $($z)?, $($xs)*)
   };
   (@method $x:expr, [$($f:tt)+]($($y:expr),*), $($z:expr)?, $($xs:tt)*) => {
      $crate::pipe!(@finish ($x).$($f)+($($y,)*$($z)?), $($xs)*)
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
   (@start $x:expr, [$($u:tt)*], match $c:tt $($xs:tt)*) => {
      $crate::pipe!(@finish match $($u)*($x) $c, $($xs)*)
   };
   (@start $x:expr, [$($u:tt)*], if $t:block else $f:block $($xs:tt)*) => {
      $crate::pipe!(@finish if $($u)*($x) $t else $f, $($xs)*)
   };
   (@start $x:expr, [$($u:tt)*], $y:tt.$f:ident $($xs:tt)*) => {
      $crate::pipe!(@method $y, [$f](), $($u)*($x), $($xs)*)
   };
   (@start $x:expr, [$($u:tt)*], $f:ident $($xs:tt)*) => {
      $crate::pipe!(@call ($($u)*($x)), [$f], $($xs)*)
   };
   (@start $x:expr, [$($u:tt)*], .$f:ident $($xs:tt)*) => {
      $crate::pipe!(@method $($u)*($x), [$f](), , $($xs)*)
   };
   (@start $x:expr, [$($u:tt)*], [.$($p:tt)+] $($xs:tt)*) => {
      $crate::pipe!(@finish ($($u)*($x)).$($p)+, $($xs)*)
   };
   (@start $x:expr, [$($u:tt)*], [$i:expr] $($xs:tt)*) => {
      $crate::pipe!(@finish ($($u)*($x))[$i], $($xs)*)
   };
   (@start $x:expr, [$($u:tt)*], |$y:pat_param| $e:block -> $($xs:tt)*) => {
      $crate::pipe!(@start (|$y| $e)($($u)*($x)), [], $($xs)*)
   };
   (@start $x:expr, [$($u:tt)*], |$y:pat_param| $e:block) => {
      (|$y| $e)($($u)*($x))
   };
   (@start $x:expr, [$($u:tt)*],) => {
      $($u)*($x)
   };
   (@init [$($x:tt)+], -> $($xs:tt)+) => {
      $crate::pipe!(@start $($x)+, [], $($xs)+)
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
   }

   use bar::*;
   use foo::*;

   #[test]
   fn test_ref() {
      assert_eq!(&0, pipe!(0 -> & -> ident));
      assert_eq!(&0, pipe!(0 -> &ident));
      assert_eq!(&mut 0, pipe!(0 -> &mut -> foo::ident));
      assert_eq!(&mut 0, pipe!(0 -> &mut foo::ident::<&mut u32>));
      assert_eq!(0, pipe!(0 -> & -> second(&1) -> *));
      assert_eq!(0, pipe!(0 -> &&second(&&1) -> **));
      assert_eq!(0, pipe!(0 -> &mut -> foo::third(&mut 1, &mut 2) -> *));
      assert_eq!(0, pipe!(0 -> &mut foo::third(&mut 1)(&mut 2) -> *));
   }

   #[test]
   fn test_try() {
      fn inner() -> Option<()> {
         assert_eq!(0, pipe!(Some(0) -> ? -> ident));
         assert_eq!(0, pipe!(Some(0) -> ?foo::ident));
         assert_eq!(0, pipe!(0 -> wrap -> ?));
         assert_eq!(0, pipe!(0 -> wrap? -> ident::<_>));
         assert_eq!(0, pipe!(Some(0) -> bar::wrap? -> ?));
         pipe!(None::<()> -> bar::wrap??);
         unreachable!();
      }
      inner();
   }

   #[test]
   fn test_method() {
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
   }

   #[test]
   fn test_index() {
      let xs = [0, 1, 2];
      assert_eq!(0, pipe!(xs -> [0]));
      assert_eq!(1, pipe!(&xs -> [1]));
      assert_eq!(2, pipe!(xs -> &[1 + 1]));
      assert_eq!(3, pipe!(xs -> &[2] -> |x| { x + 1 }));
   }

   #[test]
   fn test_access() {
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
   fn test_match() {
      assert_eq!(0, pipe!(false -> match { false => 0, true => 1}));
      assert_eq!(
         1,
         pipe!(false
            -> match { false => true, true => false}
            -> *&match { false => 0, true => 1}),
      );
   }

   #[test]
   fn test_if() {
      assert_eq!(0, pipe!(false -> if { 1 } else { 0 }));
      assert_eq!(
         1,
         pipe!(false
            -> if { false } else { true }
            -> *&if { 1 } else { 0 }),
      );
   }

   #[test]
   fn test_closure() {
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
   }

   #[test]
   fn test_combo() {
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
}
