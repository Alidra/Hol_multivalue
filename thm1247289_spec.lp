require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1247289 (d : El num) (n : El num) (p : El num) : Prf (= (∀ (λ d' : El num, (∧ (⇒ (= (+ p d) (+ n d')) (<= d (+ d' (dist ((@̦‚ num num) n p))))) (⇒ (= n (+ (+ p d) d')) (<= d (+ d' (dist ((@̦‚ num num) n p)))))))) (<= d (+ (dist ((@̦‚ num num) (+ p d) n)) (dist ((@̦‚ num num) n p)))));
