require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7216412 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ f : El (fun num real), (⇒ (∀ (λ p : El num, (⇒ (∧ (<= m p) (<= p n)) (real_le (real_of_num (NUMERAL _0)) (f p))))) (real_le (real_of_num (NUMERAL _0)) ((@sum num) (… m n) f)))))))));
