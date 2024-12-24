require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1247890 (d : El num) (m : El num) (p : El num) (n : El num) (q : El num) : Prf (= (∀ (λ d' : El num, (∧ (⇒ (= m (+ p d')) (<= d (+ d' (dist ((@̦‚ num num) n q))))) (⇒ (= p (+ m d')) (<= d (+ d' (dist ((@̦‚ num num) n q)))))))) (<= d (+ (dist ((@̦‚ num num) m p)) (dist ((@̦‚ num num) n q)))));
