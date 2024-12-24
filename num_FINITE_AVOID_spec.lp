require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4626359 : Prf (∀ (λ s : El (fun num bool), (⇒ ((@FINITE num) s) (∃ (λ a : El num, (¬ ((@IN num) a s)))))));
