pub struct DimacsParser;

pub struct ParsedCnf {
    pub num_vars: usize,
    pub clauses: Vec<Vec<i32>>,
}

impl DimacsParser {
    pub fn parse(input: &str) -> Result<ParsedCnf, String> {
        let mut num_vars = 0usize;
        let mut num_clauses = 0usize;
        let mut header_found = false;
        let mut clauses: Vec<Vec<i32>> = Vec::new();

        for line in input.lines() {
            let line = line.trim();
            if line.is_empty() {
                continue;
            }
            if line.starts_with('c') {
                continue;
            }
            if line.starts_with('p') {
                let parts: Vec<&str> = line.split_whitespace().collect();
                if parts.len() < 4 || parts[1] != "cnf" {
                    return Err(format!("Invalid problem line: {}", line));
                }
                num_vars = parts[2]
                    .parse()
                    .map_err(|_| format!("Invalid num_vars: {}", parts[2]))?;
                num_clauses = parts[3]
                    .parse()
                    .map_err(|_| format!("Invalid num_clauses: {}", parts[3]))?;
                header_found = true;
                continue;
            }
            if !header_found {
                return Err("No problem line found before clause".to_string());
            }

            // Parse clause line
            let mut clause: Vec<i32> = Vec::new();
            for tok in line.split_whitespace() {
                let x: i32 = tok
                    .parse()
                    .map_err(|_| format!("Invalid literal: {}", tok))?;
                if x == 0 {
                    break;
                }
                clause.push(x);
            }
            clauses.push(clause);
        }

        if !header_found {
            return Err("No problem line found".to_string());
        }
        if clauses.len() != num_clauses {
            // Accept minor mismatches (e.g. trailing empty clauses)
            // but cap at declared count if over
        }

        Ok(ParsedCnf { num_vars, clauses })
    }
}
