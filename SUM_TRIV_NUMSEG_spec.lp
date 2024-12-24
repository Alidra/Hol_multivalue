require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7216202 : Prf (∀ (λ f : El (fun num real), (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (< n m) (= ((@sum num) (… m n) f) (real_of_num (NUMERAL _0))))))))));
