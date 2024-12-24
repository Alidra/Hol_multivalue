require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7085797 [A] (f : El (fun A real)) : Prf (∀ (λ s : El (fun A bool), (⇒ (∀ (λ x : El A, (⇒ ((@IN A) x s) (real_le (real_of_num (NUMERAL _0)) (f x))))) (real_le (real_of_num (NUMERAL _0)) ((@sum A) s f)))));
