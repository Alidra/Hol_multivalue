require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1066212 [A] : Prf (∀ (λ f : El (fun num A), (= f ((@FCONS A) (f (NUMERAL _0)) ((@o num num A) f SUC)))));
