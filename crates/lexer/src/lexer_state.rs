use crate::Token;

#[derive(Clone)]
pub struct LexerState {
    pub position: usize,
    pub read_position: usize,
}

impl LexerState {
    pub fn ch(&self, chars: &[char]) -> Option<char> {
        chars.get(self.position).copied()
    }

    pub fn read_char(&mut self, chars: &[char]) -> Option<char> {
        let pos = self.position;
        if let Some(&ch) = chars.get(pos) {
            self.position = pos + 1;
            self.read_position += 1;
            Some(ch)
        } else {
            None
        }
    }

    pub fn read_while<F>(&mut self, chars: &[char], cond: F) -> (usize, usize)
    where
        F: Fn(char) -> bool,
    {
        let start = self.position;

        loop {
            let Some(ch) = self.ch(chars) else {
            break;
        };
            if !cond(ch) {
                break;
            }
            self.read_char(chars);
        }

        (start, self.position)
    }

    pub fn read_until<F>(&mut self, chars: &[char], cond: F) -> (usize, usize)
    where
        F: Fn(char) -> bool,
    {
        self.read_while(chars, |ch| !cond(ch))
    }

    pub fn chr(&mut self, chars: &[char], ch: char) -> Option<(usize, usize)> {
        let mut state = self.clone();
        let start = state.position;
        let c = state.read_char(chars)?;
        if c != ch {
            None
        } else {
            let end = state.position;
            *self = state;
            Some((start, end))
        }
    }

    pub fn string(&mut self, chars: &[char], s: &str) -> Option<(usize, usize)> {
        let mut state = self.clone();
        let start = state.position;
        for ch in s.chars() {
            let c = state.read_char(chars)?;
            if c != ch {
                return None;
            }
        }
        let end = state.position;
        *self = state;

        Some((start, end))
    }

    pub fn wordy<F1, F2>(
        &mut self,
        chars: &[char],
        first_char: F1,
        rest_chars: F2,
    ) -> Option<(usize, usize)>
    where
        F1: Fn(char) -> bool,
        F2: Fn(char) -> bool,
    {
        let start = self.position;
        if !first_char(self.ch(chars)?) {
            return None;
        }
        self.read_char(chars);

        let (_, end) = self.read_while(chars, rest_chars);
        Some((start, end))
    }

    pub fn cant_end_with<F1, F2>(
        &mut self,
        chars: &[char],
        contained: F1,
        not_contained: F2,
    ) -> Option<(usize, usize)>
    where
        F1: Fn(char) -> bool,
        F2: Fn(char) -> bool,
    {
        let mut state = self.clone();
        let (start, end) = state.read_while(chars, contained);
        if start == end {
            return None;
        }

        if not_contained(state.ch(chars)?) {
            return None;
        }

        *self = state;
        Some((start, end))
    }

    /// matches a sequence of <item>(<delim><item>)*
    /// there may be <whitesp> between the chunks
    pub  fn delimited<'a, F1, F2, W>(
        &mut self,
        chars: &'a [char],
        item: F1,
        delim: F2,
        whitesp: W,
    ) -> Vec<Token<'a>>
    where
        F1: Fn(&mut LexerState, &'a [char]) -> Option<Token<'a>>,
        F2: Fn(&mut LexerState, &'a [char]) -> Option<Token<'a>>,
        W: Fn(char) -> bool,
    {
        let mut state = self.clone();
        let mut out = vec![];
        state.read_while(chars, &whitesp);
        if let Some(range) = item(&mut state, chars) {
            out.push(range);
        } else {
            return vec![];
        };
        state.read_while(chars, &whitesp);

        let mut state2 = state.clone();
        while let Some(del) = delim(&mut state2, chars) {
            state2.read_while(chars, &whitesp);
            if let Some(val) = item(&mut state2, chars) {
                out.push(del);
                out.push(val);
            } else {
                break;
            }
            state2.read_while(chars, &whitesp);

            state = state2;
            state2 = state.clone();
        }

        *self = state;
        out
    }

    // fn one_of<'a>(
    //     &mut self,
    //     chars: &'a [char],
    //     funcs: &'a [&'static LexFunction],
    // ) -> Option<Token<'a>> {
    //     for f in funcs {
    //         let mut state = self.clone();
    //         if let Some(range) = f(&mut state, chars) {
    //             *self = state;
    //             return Some(range);
    //         }
    //     }
    //
    //     None
    // }

    pub fn either<'a, F1, F2>(&mut self, chars: &'a [char], f1: F1, f2: F2) -> Option<Token<'a>>
    where
        F1: FnOnce(&mut LexerState, &'a [char]) -> Option<Token<'a>>,
        F2: FnOnce(&mut LexerState, &'a [char]) -> Option<Token<'a>>,
    {
        let mut state = self.clone();
        if let Some(range) = f1(&mut state, chars) {
            *self = state;
            return Some(range);
        }

        let mut state = self.clone(); // clone should not be compiled in
        if let Some(range) = f2(&mut state, chars) {
            *self = state;
            return Some(range);
        }

        None
    }

    pub fn either3<'a, F1, F2, F3>(
        &mut self,
        chars: &'a [char],
        f1: F1,
        f2: F2,
        f3: F3,
    ) -> Option<Token<'a>>
    where
        F1: FnOnce(&mut LexerState, &'a [char]) -> Option<Token<'a>>,
        F2: FnOnce(&mut LexerState, &'a [char]) -> Option<Token<'a>>,
        F3: FnOnce(&mut LexerState, &'a [char]) -> Option<Token<'a>>,
    {
        let mut state = self.clone();
        if let Some(range) = f1(&mut state, chars) {
            *self = state;
            return Some(range);
        }

        let mut state = self.clone(); // clone should not be compiled in
        if let Some(range) = f2(&mut state, chars) {
            *self = state;
            return Some(range);
        }

        let mut state = self.clone(); // clone should not be compiled in
        if let Some(range) = f3(&mut state, chars) {
            *self = state;
            return Some(range);
        }

        None
    }

    #[allow(unused)]
    fn seq<F1, F2>(&mut self, chars: &[char], f1: F1, f2: F2) -> Option<(usize, usize)>
    where
        F1: FnOnce(&mut LexerState, &[char]) -> Option<(usize, usize)>,
        F2: FnOnce(&mut LexerState, &[char]) -> Option<(usize, usize)>,
    {
        let mut state = self.clone();
        let (start, _) = f1(&mut state, chars)?;
        let (_, end) = f2(&mut state, chars)?;

        Some((start, end))
    }
}

