require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3464376 [_89837 _89861 _89862 _89863] (P : El (fun _89863 (fun _89862 (fun _89861 bool)))) (f : El (fun _89863 (fun _89862 (fun _89861 (fun _89837 bool))))) : Prf (= ((@INTERS _89837) ((@GSPEC (fun _89837 bool)) (λ GEN_PVAR_59 : El (fun _89837 bool), (∃ (λ x : El _89863, (∃ (λ y : El _89862, (∃ (λ z : El _89861, ((@SETSPEC (fun _89837 bool)) GEN_PVAR_59 (P x y z) (f x y z))))))))))) ((@GSPEC _89837) (λ GEN_PVAR_60 : El _89837, (∃ (λ a : El _89837, ((@SETSPEC _89837) GEN_PVAR_60 (∀ (λ x : El _89863, (∀ (λ y : El _89862, (∀ (λ z : El _89861, (⇒ (P x y z) ((@IN _89837) a (f x y z))))))))) a))))));
