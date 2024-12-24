require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6377849 [A] : Prf (∀ (λ op : El (fun A (fun A A)), (⇒ ((@monoidal A) op) (∀ (λ x : El (fun num A), (∀ (λ m : El num, (∀ (λ n : El num, (= ((@iterate A num) op (… m n) x) ((@COND A) (< n m) ((@neutral A) op) ((@iterate A num) op (… (NUMERAL _0) (- n m)) (λ i : El num, (x (- n i)))))))))))))));
