require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7048726 : Prf (∀ (λ p : El num, (∀ (λ f : El (fun num num), (∀ (λ m : El num, (∀ (λ n : El num, (= ((@nsum num) (… (+ m p) (+ n p)) f) ((@nsum num) (… m n) (λ i : El num, (f (+ i p)))))))))))));
