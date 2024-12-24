require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5418323 : Prf (= (∀ (λ m : El num, (∀ (λ n : El num, (= (… m (SUC n)) ((@COND (fun num bool)) (<= m (SUC n)) ((@INSERT num) (SUC n) (… m n)) (… m n))))))) (∀ (λ m : El num, (∀ (λ n : El num, (= (… m (SUC n)) ((@COND (fun num bool)) (<= m (SUC n)) ((@INSERT num) (SUC n) (… m n)) (… m n))))))));
