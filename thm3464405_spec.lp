require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3464405 [_89711 _89725] : Prf (∀ (λ P : El (fun _89725 bool), (∀ (λ f : El (fun _89725 (fun _89711 bool)), (= ((@INTERS _89711) ((@GSPEC (fun _89711 bool)) (λ GEN_PVAR_55 : El (fun _89711 bool), (∃ (λ x : El _89725, ((@SETSPEC (fun _89711 bool)) GEN_PVAR_55 (P x) (f x))))))) ((@GSPEC _89711) (λ GEN_PVAR_56 : El _89711, (∃ (λ a : El _89711, ((@SETSPEC _89711) GEN_PVAR_56 (∀ (λ x : El _89725, (⇒ (P x) ((@IN _89711) a (f x))))) a))))))))));
