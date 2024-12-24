require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem177911 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (⇒ (∧ (< m p) (< n p)) (= (MOD (+ m n) p) ((@COND num) (< (+ m n) p) (+ m n) (- (+ m n) p))))))))));
