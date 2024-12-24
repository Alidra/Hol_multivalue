require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1103188 [_25376] : Prf (∧ (∀ (λ x : El _25376, (= ((@MEM _25376) x (@NIL _25376)) F))) (∀ (λ h : El _25376, (∀ (λ x : El _25376, (∀ (λ t : El (list _25376), (= ((@MEM _25376) x ((@CONS _25376) h t)) (∨ (= x h) ((@MEM _25376) x t))))))))));
