require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8440918 [_147009 _147011 _147015] (<< : El (fun _147009 (fun _147009 bool))) (s : El (fun _147015 _147009)) (t : El (fun (fun _147009 _147011) (fun _147015 _147011))) : Prf (= ((@superadmissible _147009 _147011 _147015) << (λ f : El (fun _147009 _147011), (λ x : El _147015, T)) s t) ((@tailadmissible _147009 _147011 _147015) << (λ f : El (fun _147009 _147011), (λ x : El _147015, T)) s t));
