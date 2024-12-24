require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1247464 (n : El num) (m : El num) (d : El num) : Prf (= (∀ (λ d' : El num, (∧ (⇒ (= m (+ n d')) (<= d (+ d' (dist ((@̦‚ num num) n (+ m d)))))) (⇒ (= n (+ m d')) (<= d (+ d' (dist ((@̦‚ num num) n (+ m d))))))))) (<= d (+ (dist ((@̦‚ num num) m n)) (dist ((@̦‚ num num) n (+ m d))))));
