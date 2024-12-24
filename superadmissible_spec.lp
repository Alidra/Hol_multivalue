require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8096071 [_143606 _143608 _143614] : Prf (∀ (λ << : El (fun _143606 (fun _143606 bool)), (∀ (λ p : El (fun (fun _143606 _143608) (fun _143614 bool)), (∀ (λ s : El (fun _143614 _143606), (∀ (λ t : El (fun (fun _143606 _143608) (fun _143614 _143608)), (= ((@superadmissible _143606 _143608 _143614) << p s t) (⇒ ((@admissible _143606 _143608 _143606 bool _143614) << (λ f : El (fun _143606 _143608), (λ a : El _143614, T)) s p) ((@tailadmissible _143606 _143608 _143614) << p s t)))))))))));
