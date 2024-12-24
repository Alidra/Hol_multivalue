require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7223171 : Prf (∀ (λ p : El num, (∀ (λ f : El (fun num real), (∀ (λ m : El num, (∀ (λ n : El num, (= ((@sum num) (… (+ m p) (+ n p)) f) ((@sum num) (… m n) (λ i : El num, (f (+ i p)))))))))))));
