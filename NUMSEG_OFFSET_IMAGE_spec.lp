require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5470571 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (= (… (+ m p) (+ n p)) ((@IMAGE num num) (λ i : El num, (+ i p)) (… m n)))))))));
