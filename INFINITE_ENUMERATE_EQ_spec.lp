require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4774262 : Prf (∀ (λ s : El (fun num bool), (= ((@INFINITE num) s) (∃ (λ r : El (fun num num), (∧ (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (< m n) (< (r m) (r n))))))) (= ((@IMAGE num num) r (@UNIV num)) s)))))));
