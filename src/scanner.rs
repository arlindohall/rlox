
pub struct Scanner {
    text: String,
}

impl Scanner {
    pub fn scan_tokens(&self) -> Vec<String> {
        let mut tokens = Vec::new();
        for item in self.text.split(" ") {
            tokens.push(String::from(item));
        }
        return tokens;
    }

    pub fn new(snippet: &str) -> Scanner {
        Scanner {
            text: String::from(snippet)
        }
    }
}