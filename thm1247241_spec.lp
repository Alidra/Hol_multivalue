require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1247241 (m : El num) (n : El num) (p : El num) : Prf (= (∀ (λ d : El num, (∧ (⇒ (= m (+ p d)) (<= d (+ (dist ((@̦‚ num num) m n)) (dist ((@̦‚ num num) n p))))) (⇒ (= p (+ m d)) (<= d (+ (dist ((@̦‚ num num) m n)) (dist ((@̦‚ num num) n p)))))))) (<= (dist ((@̦‚ num num) m p)) (+ (dist ((@̦‚ num num) m n)) (dist ((@̦‚ num num) n p)))));
