// THE OUTPUT OF THIS EXAMPLE IS NOT CHECKED TO MATCH ITS `.out` FILE.
//
// MAKE SURE TO UPDATE THE `.out` FILE IF YOU CHANGE IT.
//
// bash:
// > rustc -o /tmp/grouping src/strength/code/<file> && /tmp/grouping > src/strength/code/<file>.out

// ANCHOR: all
#![allow(non_upper_case_globals)]

// ANCHOR: struct
pub struct Wrap<T, const len: usize> {
    arr: [T; len],
    grouping: usize,
}
// ANCHOR_END: struct
impl<T, const len: usize> Wrap<T, len> {
    // ANCHOR: constructor_check
    /// Constructor.
    pub fn new(arr: [T; len], grouping: usize) -> Self {
        if len % grouping != 0 {
            panic!(
                "grouping value {} is not a multiple of array length ({})",
                grouping, len,
            );
        }
        if grouping < 1 {
            panic!("illegal grouping value {}, must be > 0", grouping)
        }
        // ANCHOR_END: constructor_check
        Self { arr, grouping }
    }
    // ANCHOR: fold
    /// Grouped fold.
    pub fn fold<Acc>(&self, init: Acc, mut next: impl FnMut(Acc, &[T]) -> Acc) -> Acc {
        let (arr, grouping) = (&self.arr, self.grouping);
        // ANCHOR: fold_body
        let mut acc = init;
        let mut i = 0;
        while i < len {
            let next_i = i + grouping;
            acc = next(acc, &arr[i..next_i]);
            i = next_i
        }
        acc
        // ANCHOR_END: fold_body
    }
    // ANCHOR_END: fold
}

// ANCHOR: main
fn main() {
    // `len` ~~~~~~v
    let arr: [f64; 6] = [0., 1., 2., 3., 4., 5.];
    // `grouping` ~~~~~~~~~~~~v
    let wrap = Wrap::new(arr, 3);
    let value_1 = wrap.fold(0., |acc, arr| {
        println!(
            "len: {} | arr[0]: {}, arr[1]: {}, arr[2]: {}",
            arr.len(),
            arr[0],
            arr[1],
            arr[2]
        );
        assert_eq!(arr.len(), 3);
        let new_acc = acc + arr[0] * arr[1] * arr[2];
        println!("acc: {}, new_acc: {}", acc, new_acc);
        new_acc
    });
    println!("fold result: {}", value_1);

    println!("\n---------------------\n");

    // `len` ~~~~~~v
    let arr: [f64; 6] = [0., 1., 2., 3., 4., 5.];
    // `grouping` ~~~~~~~~~~~~v
    let wrap = Wrap::new(arr, 2);
    let value_2 = wrap.fold(0., |acc, arr| {
        println!(
            "len: {} | arr[0]: {}, arr[1]: {}",
            arr.len(),
            arr[0],
            arr[1]
        );
        assert_eq!(arr.len(), 2);
        let new_acc = acc + arr[0] * arr[1];
        println!("acc: {}, new_acc: {}", acc, new_acc);
        new_acc
    });
    println!("fold result: {}", value_2);
}
// ANCHOR_END: main
// ANCHOR_END: all
