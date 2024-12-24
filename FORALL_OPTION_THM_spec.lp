require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1072225 [_24424] : Prf (∀ (λ P : El (fun (option _24424) bool), (= (∀ (λ x : El (option _24424), (P x))) (∧ (P (@NONE _24424)) (∀ (λ a : El _24424, (P ((@SOME _24424) a))))))));
