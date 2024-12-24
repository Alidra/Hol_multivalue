require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3464377 [_89769 _89788 _89789] (P : El (fun _89789 (fun _89788 bool))) (f : El (fun _89789 (fun _89788 (fun _89769 bool)))) : Prf (= ((@INTERS _89769) ((@GSPEC (fun _89769 bool)) (λ GEN_PVAR_57 : El (fun _89769 bool), (∃ (λ x : El _89789, (∃ (λ y : El _89788, ((@SETSPEC (fun _89769 bool)) GEN_PVAR_57 (P x y) (f x y))))))))) ((@GSPEC _89769) (λ GEN_PVAR_58 : El _89769, (∃ (λ a : El _89769, ((@SETSPEC _89769) GEN_PVAR_58 (∀ (λ x : El _89789, (∀ (λ y : El _89788, (⇒ (P x y) ((@IN _89769) a (f x y))))))) a))))));
