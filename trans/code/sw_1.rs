type Int = i64;
struct State {
    start_stop: bool,
    reset: bool,
    is_counting: bool,
    cnt: Int, // arbitrary precision integer (ℕ)
}
impl State {
    fn init(start_stop: bool, reset: bool, random_cnt: Int) -> State {
        State {
            start_stop,
            reset,
            // Initially not counting, unless `start_stop` is pressed
            // and triggers counting.
            is_counting: start_stop,
            cnt: if reset { 0 } else { random_cnt },
        }
    }
    fn step(&mut self, start_stop: bool, reset: bool) {
        self.start_stop = start_stop;
        self.reset = reset;
        // Need to toggle `self.is_counting`?
        if self.start_stop {
            self.is_counting = !self.is_counting
        }
        // `cnt` update
        self.cnt = if self.reset {
            0
        } else if self.is_counting {
            self.cnt + 1
        } else {
            self.cnt
        };
    }
    fn to_string(&self) -> String {
        format!(
            "cnt: {}, {}counting",
            self.cnt,
            if self.is_counting { "" } else { "not " }
        )
    }
}

fn main() {
    let mut state = State::init(false, false, -71);
    let mut step_count = 0;
    println!("initial state: {}", state.to_string());

    let mut step_show = |start_stop, reset, count_check| {
        if start_stop {
            println!("`start_stop` pressed")
        }
        if reset {
            println!("`reset` pressed")
        }
        state.step(start_stop, reset);
        step_count += 1;
        println!("@{} | {}", step_count, state.to_string());
        assert_eq!(state.cnt, count_check);
    };

    step_show(true, false, -70);
    step_show(false, false, -69);
    step_show(false, false, -68);
    step_show(false, false, -67);
    step_show(false, true, 0);
    step_show(false, false, 1);
    step_show(false, false, 2);
    step_show(false, false, 3);
    step_show(true, false, 3);
    step_show(false, false, 3);
    step_show(false, false, 3);
}
