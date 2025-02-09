```rust
fn dederef(x: &&u32) -> u32 {
   **x
}

fn lol(xs: &[u32], ys: &[usize]) -> Option<u32> {
   // An even worse way of writing `Some(dederef(&xs.get(*ys.get(123)?)?))`
   pipe!(ys -> .get(123) -> ?*xs.get -> ?&dederef -> Some)
}
```
