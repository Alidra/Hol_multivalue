Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARBITRARY_INTERSECTION_OF_UNION_EQ_term_abbrevs.
Require Import ARBITRARY_INTERSECTION_OF_COMPLEMENT_spec.
Require Import ARBITRARY_UNION_OF_INTER_EQ_spec.
Require Import COMPL_COMPL_spec.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Lemma lem4872158 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3270825 A s). Qed.
Lemma lem4872159 {A : Type'} (s : A -> Prop) : (term0 A s) = ((term1 A s) = s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem4872172 (p : Prop) : p = (term2 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4872173 {_111961 : Type'} (P : type686 _111961) : ((term3 _111961 P) = (term4 _111961 P)) = (term5 _111961 P).
Proof. exact (@lem4872172 ((term3 _111961 P) = (term4 _111961 P))). Qed.
Lemma lem4872174 {_111961 : Type'} (P : type686 _111961) : (term5 _111961 P) = ((term3 _111961 P) = (term4 _111961 P)).
Proof. exact (SYM (@lem4872173 _111961 P)). Qed.
Lemma lem4872175 {_111961 : Type'} (P : type686 _111961) (h1 : term6 _111961 P) : term6 _111961 P.
Proof. exact (h1). Qed.
Lemma lem4872176 {_111961 : Type'} : term7 _111961.
Proof. exact (@lem3270825 _111961). Qed.
Lemma lem4872180 {_111961 : Type'} (P : type686 _111961) (h1 : term8 _111961 P) : term8 _111961 P.
Proof. exact (h1). Qed.
Lemma lem4872181 {_111961 : Type'} (P : type686 _111961) : term9 _111961 P.
Proof. exact (fun h0 : term8 _111961 P => @lem4872180 _111961 P h0). Qed.
Lemma lem4872182 {_111961 : Type'} (P : type686 _111961) (h1 : term9 _111961 P) : term9 _111961 P.
Proof. exact (h1). Qed.
Lemma lem4872183 {_111961 : Type'} (P : type686 _111961) (h1 : term8 _111961 P) : term8 _111961 P.
Proof. exact (h1). Qed.
Lemma lem4872184 {_111961 : Type'} (P : type686 _111961) (h1 : term8 _111961 P) (h2 : term9 _111961 P) : term8 _111961 P.
Proof. exact (@lem4872182 _111961 P h2 (@lem4872183 _111961 P h1)). Qed.
Lemma lem4872185 {_111961 : Type'} (P : type686 _111961) (h1 : term8 _111961 P) : term10 _111961 P.
Proof. exact (fun h0 : term9 _111961 P => @lem4872184 _111961 P h1 h0). Qed.
Lemma lem4872186 {_111961 : Type'} (P : type686 _111961) (h1 : term9 _111961 P) : term9 _111961 P.
Proof. exact (h1). Qed.
Lemma lem4872187 {_111961 : Type'} (P : type686 _111961) (h1 : term8 _111961 P) (h2 : term9 _111961 P) : term8 _111961 P.
Proof. exact (@lem4872185 _111961 P h1 (@lem4872186 _111961 P h2)). Qed.
Lemma lem4872188 {_111961 : Type'} (P : type686 _111961) (h1 : term9 _111961 P) : term9 _111961 P.
Proof. exact (fun h0 : term8 _111961 P => @lem4872187 _111961 P h0 h1). Qed.
Lemma lem4872189 {_111961 : Type'} (P : type686 _111961) : term11 _111961 P.
Proof. exact (fun h0 : term9 _111961 P => @lem4872188 _111961 P h0). Qed.
Lemma lem4872192 {_111961 : Type'} (P : type686 _111961) : term9 _111961 P.
Proof. exact (@lem4872189 _111961 P (@lem4872181 _111961 P)). Qed.
Lemma lem4872193 {_111961 : Type'} (P : type686 _111961) : term9 _111961 P.
Proof. exact (@lem4872192 _111961 P). Qed.
Lemma lem4872209 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4872210 {_111961 : Type'} : (term12 _111961) = (term13 _111961).
Proof. exact (@lem4872209 (term7 _111961)). Qed.
Lemma lem4872215 {_111961 : Type'} (P : type686 _111961) : (term14 _111961 P) = (term14 _111961 P).
Proof. exact (eq_refl (term14 _111961 P)). Qed.
Lemma lem4872216 {_111961 : Type'} (P : type686 _111961) : (term8 _111961 P) = (term15 _111961 P).
Proof. exact (MK_COMB (@lem4872215 _111961 P) (@lem4872210 _111961)). Qed.
Lemma lem4872219 {_111961 : Type'} : (term16 _111961) = (term17 _111961).
Proof. exact (fun_ext (fun P : type686 _111961 => @lem4872216 _111961 P)). Qed.
Lemma lem4872220 {_111961 : Type'} : (@all ((_111961 -> Prop) -> Prop)) = (@all ((_111961 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111961 -> Prop) -> Prop))). Qed.
Lemma lem4872229 {_111961 : Type'} : (term18 _111961) = (term19 _111961).
Proof. exact (MK_COMB (@lem4872220 _111961) (@lem4872219 _111961)). Qed.
Lemma lem4872230 {_111961 : Type'} (s : _111961 -> Prop) : ((term1 _111961 s) = s) = ((term1 _111961 s) = s).
Proof. exact (eq_refl ((term1 _111961 s) = s)). Qed.
Lemma lem4872231 {_111961 : Type'} : (term20 _111961) = (term20 _111961).
Proof. exact (fun_ext (fun s : _111961 -> Prop => @lem4872230 _111961 s)). Qed.
Lemma lem4872232 {_111961 : Type'} : (@all (_111961 -> Prop)) = (@all (_111961 -> Prop)).
Proof. exact (eq_refl (@all (_111961 -> Prop))). Qed.
Lemma lem4872233 {_111961 : Type'} : (term7 _111961) = (term7 _111961).
Proof. exact (MK_COMB (@lem4872232 _111961) (@lem4872231 _111961)). Qed.
Lemma lem4872234 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4872235 {_111961 : Type'} : (term13 _111961) = (term13 _111961).
Proof. exact (MK_COMB (@lem4872234) (@lem4872233 _111961)). Qed.
Lemma lem4872236 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem4872237 {_111961 : Type'} (P : type686 _111961) : (term21 _111961 P) = (term21 _111961 P).
Proof. exact (fun_ext (fun s : _111961 -> Prop => @lem4872236 _111961 P s)). Qed.
Lemma lem4872238 {_111961 : Type'} : (@all (_111961 -> Prop)) = (@all (_111961 -> Prop)).
Proof. exact (eq_refl (@all (_111961 -> Prop))). Qed.
Lemma lem4872239 {_111961 : Type'} (P : type686 _111961) : (term4 _111961 P) = (term4 _111961 P).
Proof. exact (MK_COMB (@lem4872238 _111961) (@lem4872237 _111961 P)). Qed.
Lemma lem4872240 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (term22 _111961 P s) = (term22 _111961 P s).
Proof. exact (eq_refl (term22 _111961 P s)). Qed.
Lemma lem4872241 {_111961 : Type'} (P : type686 _111961) : (term23 _111961 P) = (term23 _111961 P).
Proof. exact (fun_ext (fun s : _111961 -> Prop => @lem4872240 _111961 P s)). Qed.
Lemma lem4872242 {_111961 : Type'} : (@all (_111961 -> Prop)) = (@all (_111961 -> Prop)).
Proof. exact (eq_refl (@all (_111961 -> Prop))). Qed.
Lemma lem4872243 {_111961 : Type'} (P : type686 _111961) : (term3 _111961 P) = (term3 _111961 P).
Proof. exact (MK_COMB (@lem4872242 _111961) (@lem4872241 _111961 P)). Qed.
Lemma lem4872244 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4872245 {_111961 : Type'} (P : type686 _111961) : (term24 _111961 P) = (term24 _111961 P).
Proof. exact (MK_COMB (@lem4872244) (@lem4872243 _111961 P)). Qed.
Lemma lem4872246 {_111961 : Type'} (P : type686 _111961) : ((term3 _111961 P) = (term4 _111961 P)) = ((term3 _111961 P) = (term4 _111961 P)).
Proof. exact (MK_COMB (@lem4872245 _111961 P) (@lem4872239 _111961 P)). Qed.
Lemma lem4872247 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4872248 {_111961 : Type'} (P : type686 _111961) : (term6 _111961 P) = (term6 _111961 P).
Proof. exact (MK_COMB (@lem4872247) (@lem4872246 _111961 P)). Qed.
Lemma lem4872249 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4872250 {_111961 : Type'} (P : type686 _111961) : (term14 _111961 P) = (term14 _111961 P).
Proof. exact (MK_COMB (@lem4872249) (@lem4872248 _111961 P)). Qed.
Lemma lem4872251 {_111961 : Type'} (P : type686 _111961) : (term15 _111961 P) = (term15 _111961 P).
Proof. exact (MK_COMB (@lem4872250 _111961 P) (@lem4872235 _111961)). Qed.
Lemma lem4872252 {_111961 : Type'} : (term17 _111961) = (term17 _111961).
Proof. exact (fun_ext (fun P : type686 _111961 => @lem4872251 _111961 P)). Qed.
Lemma lem4872253 {_111961 : Type'} : (@all ((_111961 -> Prop) -> Prop)) = (@all ((_111961 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111961 -> Prop) -> Prop))). Qed.
Lemma lem4872254 {_111961 : Type'} : (term19 _111961) = (term19 _111961).
Proof. exact (MK_COMB (@lem4872253 _111961) (@lem4872252 _111961)). Qed.
Lemma lem4872283 {_111961 : Type'} : (term18 _111961) = (term19 _111961).
Proof. exact (TRANS (@lem4872229 _111961) (@lem4872254 _111961)). Qed.
Lemma lem4872284 {_111961 : Type'} : (term19 _111961) = (term18 _111961).
Proof. exact (SYM (@lem4872283 _111961)). Qed.
Lemma lem4872285 {_111961 : Type'} (P : type686 _111961) (h1 : term6 _111961 P) : term6 _111961 P.
Proof. exact (h1). Qed.
Lemma lem4872286 {_111961 : Type'} (h1 : term7 _111961) : term7 _111961.
Proof. exact (h1). Qed.
Lemma lem4872288 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (term22 _111961 P s) = (term22 _111961 P s).
Proof. exact (eq_refl (term22 _111961 P s)). Qed.
Lemma lem4872289 {_111961 : Type'} (P : type686 _111961) : (term25 _111961 P) = (term26 _111961 P).
Proof. exact (@lem18392 (_111961 -> Prop) P). Qed.
Lemma lem4872290 {_111961 : Type'} (P : type686 _111961) : (term27 _111961 P) = (term28 _111961 P).
Proof. exact (@lem4872289 _111961 (term23 _111961 P)). Qed.
Lemma lem4872291 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (term29 _111961 P s) = (term22 _111961 P s).
Proof. exact (eq_refl (term29 _111961 P s)). Qed.
Lemma lem4872292 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4872294 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (term30 _111961 P s) = (term31 _111961 P s).
Proof. exact (MK_COMB (@lem4872292) (@lem4872291 _111961 P s)). Qed.
Lemma lem4872295 {_111961 : Type'} (P : type686 _111961) : (term32 _111961 P) = (term33 _111961 P).
Proof. exact (fun_ext (fun s : _111961 -> Prop => @lem4872294 _111961 P s)). Qed.
Lemma lem4872296 {_111961 : Type'} : (@ex (_111961 -> Prop)) = (@ex (_111961 -> Prop)).
Proof. exact (eq_refl (@ex (_111961 -> Prop))). Qed.
Lemma lem4872297 {_111961 : Type'} (P : type686 _111961) : (term28 _111961 P) = (term34 _111961 P).
Proof. exact (MK_COMB (@lem4872296 _111961) (@lem4872295 _111961 P)). Qed.
Lemma lem4872298 {_111961 : Type'} (P : type686 _111961) : (term27 _111961 P) = (term34 _111961 P).
Proof. exact (TRANS (@lem4872290 _111961 P) (@lem4872297 _111961 P)). Qed.
Lemma lem4872299 {_111961 : Type'} (P : type686 _111961) : (term23 _111961 P) = (term23 _111961 P).
Proof. exact (fun_ext (fun s : _111961 -> Prop => @lem4872288 _111961 P s)). Qed.
Lemma lem4872300 {_111961 : Type'} : (@all (_111961 -> Prop)) = (@all (_111961 -> Prop)).
Proof. exact (eq_refl (@all (_111961 -> Prop))). Qed.
Lemma lem4872301 {_111961 : Type'} (P : type686 _111961) : (term3 _111961 P) = (term3 _111961 P).
Proof. exact (MK_COMB (@lem4872300 _111961) (@lem4872299 _111961 P)). Qed.
Lemma lem4872303 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem4872304 {_111961 : Type'} (P : type686 _111961) : (term25 _111961 P) = (term26 _111961 P).
Proof. exact (@lem18392 (_111961 -> Prop) P). Qed.
Lemma lem4872305 {_111961 : Type'} (P : type686 _111961) : (term35 _111961 P) = (term36 _111961 P).
Proof. exact (@lem4872304 _111961 (term21 _111961 P)). Qed.
Lemma lem4872306 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (term37 _111961 P s) = (P s).
Proof. exact (eq_refl (term37 _111961 P s)). Qed.
Lemma lem4872307 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4872309 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (term38 _111961 P s) = (term39 _111961 P s).
Proof. exact (MK_COMB (@lem4872307) (@lem4872306 _111961 P s)). Qed.
Lemma lem4872310 {_111961 : Type'} (P : type686 _111961) : (term40 _111961 P) = (term41 _111961 P).
Proof. exact (fun_ext (fun s : _111961 -> Prop => @lem4872309 _111961 P s)). Qed.
Lemma lem4872311 {_111961 : Type'} : (@ex (_111961 -> Prop)) = (@ex (_111961 -> Prop)).
Proof. exact (eq_refl (@ex (_111961 -> Prop))). Qed.
Lemma lem4872312 {_111961 : Type'} (P : type686 _111961) : (term36 _111961 P) = (term26 _111961 P).
Proof. exact (MK_COMB (@lem4872311 _111961) (@lem4872310 _111961 P)). Qed.
Lemma lem4872313 {_111961 : Type'} (P : type686 _111961) : (term35 _111961 P) = (term26 _111961 P).
Proof. exact (TRANS (@lem4872305 _111961 P) (@lem4872312 _111961 P)). Qed.
Lemma lem4872314 {_111961 : Type'} (P : type686 _111961) : (term21 _111961 P) = (term21 _111961 P).
Proof. exact (fun_ext (fun s : _111961 -> Prop => @lem4872303 _111961 P s)). Qed.
Lemma lem4872315 {_111961 : Type'} : (@all (_111961 -> Prop)) = (@all (_111961 -> Prop)).
Proof. exact (eq_refl (@all (_111961 -> Prop))). Qed.
Lemma lem4872316 {_111961 : Type'} (P : type686 _111961) : (term4 _111961 P) = (term4 _111961 P).
Proof. exact (MK_COMB (@lem4872315 _111961) (@lem4872314 _111961 P)). Qed.
Lemma lem4872317 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4872318 {_111961 : Type'} (P : type686 _111961) : (term42 _111961 P) = (term43 _111961 P).
Proof. exact (MK_COMB (@lem4872317) (@lem4872298 _111961 P)). Qed.
Lemma lem4872319 {_111961 : Type'} (P : type686 _111961) : (term44 _111961 P) = (term45 _111961 P).
Proof. exact (MK_COMB (@lem4872318 _111961 P) (@lem4872316 _111961 P)). Qed.
Lemma lem4872320 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4872321 {_111961 : Type'} (P : type686 _111961) : (term46 _111961 P) = (term46 _111961 P).
Proof. exact (MK_COMB (@lem4872320) (@lem4872301 _111961 P)). Qed.
Lemma lem4872322 {_111961 : Type'} (P : type686 _111961) : (term47 _111961 P) = (term48 _111961 P).
Proof. exact (MK_COMB (@lem4872321 _111961 P) (@lem4872313 _111961 P)). Qed.
Lemma lem4872323 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4872324 {_111961 : Type'} (P : type686 _111961) : (term49 _111961 P) = (term50 _111961 P).
Proof. exact (MK_COMB (@lem4872323) (@lem4872322 _111961 P)). Qed.
Lemma lem4872325 {_111961 : Type'} (P : type686 _111961) : (term51 _111961 P) = (term52 _111961 P).
Proof. exact (MK_COMB (@lem4872324 _111961 P) (@lem4872319 _111961 P)). Qed.
Lemma lem4872326 {_111961 : Type'} (P : type686 _111961) : (term6 _111961 P) = (term51 _111961 P).
Proof. exact (@lem17646 (term3 _111961 P) (term4 _111961 P)). Qed.
Lemma lem4872327 {_111961 : Type'} (P : type686 _111961) : (term6 _111961 P) = (term52 _111961 P).
Proof. exact (TRANS (@lem4872326 _111961 P) (@lem4872325 _111961 P)). Qed.
Lemma lem4872346 {A : Type'} (P : Prop) (Q : A -> Prop) : (term53 A P Q) = (term54 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4872347 {_111961 : Type'} (P : Prop) (Q : type686 _111961) : (term55 _111961 P Q) = (term56 _111961 P Q).
Proof. exact (@lem4872346 (_111961 -> Prop) P Q). Qed.
Lemma lem4872348 {_111961 : Type'} (P : type686 _111961) : (term57 _111961 P) = (term58 _111961 P).
Proof. exact (@lem4872347 _111961 (term3 _111961 P) (term41 _111961 P)). Qed.
Lemma lem4872349 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (term59 _111961 P s) = (term39 _111961 P s).
Proof. exact (eq_refl (term59 _111961 P s)). Qed.
Lemma lem4872350 {_111961 : Type'} (P : type686 _111961) : (term60 _111961 P) = (term41 _111961 P).
Proof. exact (fun_ext (fun s : _111961 -> Prop => @lem4872349 _111961 P s)). Qed.
Lemma lem4872351 {_111961 : Type'} : (@ex (_111961 -> Prop)) = (@ex (_111961 -> Prop)).
Proof. exact (eq_refl (@ex (_111961 -> Prop))). Qed.
Lemma lem4872352 {_111961 : Type'} (P : type686 _111961) : (term61 _111961 P) = (term26 _111961 P).
Proof. exact (MK_COMB (@lem4872351 _111961) (@lem4872350 _111961 P)). Qed.
Lemma lem4872353 {_111961 : Type'} (P : type686 _111961) : (term46 _111961 P) = (term46 _111961 P).
Proof. exact (eq_refl (term46 _111961 P)). Qed.
Lemma lem4872354 {_111961 : Type'} (P : type686 _111961) : (term57 _111961 P) = (term48 _111961 P).
Proof. exact (MK_COMB (@lem4872353 _111961 P) (@lem4872352 _111961 P)). Qed.
Lemma lem4872355 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4872356 {_111961 : Type'} (P : type686 _111961) : (term62 _111961 P) = (term63 _111961 P).
Proof. exact (MK_COMB (@lem4872355) (@lem4872354 _111961 P)). Qed.
Lemma lem4872357 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (term59 _111961 P s) = (term39 _111961 P s).
Proof. exact (eq_refl (term59 _111961 P s)). Qed.
Lemma lem4872358 {_111961 : Type'} (P : type686 _111961) : (term46 _111961 P) = (term46 _111961 P).
Proof. exact (eq_refl (term46 _111961 P)). Qed.
Lemma lem4872359 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (term64 _111961 P s) = (term65 _111961 P s).
Proof. exact (MK_COMB (@lem4872358 _111961 P) (@lem4872357 _111961 P s)). Qed.
Lemma lem4872360 {_111961 : Type'} (P : type686 _111961) : (term66 _111961 P) = (term67 _111961 P).
Proof. exact (fun_ext (fun s : _111961 -> Prop => @lem4872359 _111961 P s)). Qed.
Lemma lem4872361 {_111961 : Type'} : (@ex (_111961 -> Prop)) = (@ex (_111961 -> Prop)).
Proof. exact (eq_refl (@ex (_111961 -> Prop))). Qed.
Lemma lem4872362 {_111961 : Type'} (P : type686 _111961) : (term58 _111961 P) = (term68 _111961 P).
Proof. exact (MK_COMB (@lem4872361 _111961) (@lem4872360 _111961 P)). Qed.
Lemma lem4872363 {_111961 : Type'} (P : type686 _111961) : ((term57 _111961 P) = (term58 _111961 P)) = ((term48 _111961 P) = (term68 _111961 P)).
Proof. exact (MK_COMB (@lem4872356 _111961 P) (@lem4872362 _111961 P)). Qed.
Lemma lem4872364 {_111961 : Type'} (P : type686 _111961) : (term48 _111961 P) = (term68 _111961 P).
Proof. exact (EQ_MP (@lem4872363 _111961 P) (@lem4872348 _111961 P)). Qed.
Lemma lem4872365 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4872366 {_111961 : Type'} (P : type686 _111961) : (term50 _111961 P) = (term69 _111961 P).
Proof. exact (MK_COMB (@lem4872365) (@lem4872364 _111961 P)). Qed.
Lemma lem4872368 {A : Type'} (P : A -> Prop) (Q : Prop) : (term70 A P Q) = (term71 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4872369 {_111961 : Type'} (P : type686 _111961) (Q : Prop) : (term72 _111961 P Q) = (term73 _111961 P Q).
Proof. exact (@lem4872368 (_111961 -> Prop) P Q). Qed.
Lemma lem4872370 {_111961 : Type'} (P : type686 _111961) : (term74 _111961 P) = (term75 _111961 P).
Proof. exact (@lem4872369 _111961 (term33 _111961 P) (term4 _111961 P)). Qed.
Lemma lem4872371 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (term76 _111961 P s) = (term31 _111961 P s).
Proof. exact (eq_refl (term76 _111961 P s)). Qed.
Lemma lem4872372 {_111961 : Type'} (P : type686 _111961) : (term77 _111961 P) = (term33 _111961 P).
Proof. exact (fun_ext (fun s : _111961 -> Prop => @lem4872371 _111961 P s)). Qed.
Lemma lem4872373 {_111961 : Type'} : (@ex (_111961 -> Prop)) = (@ex (_111961 -> Prop)).
Proof. exact (eq_refl (@ex (_111961 -> Prop))). Qed.
Lemma lem4872374 {_111961 : Type'} (P : type686 _111961) : (term78 _111961 P) = (term34 _111961 P).
Proof. exact (MK_COMB (@lem4872373 _111961) (@lem4872372 _111961 P)). Qed.
Lemma lem4872375 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4872376 {_111961 : Type'} (P : type686 _111961) : (term79 _111961 P) = (term43 _111961 P).
Proof. exact (MK_COMB (@lem4872375) (@lem4872374 _111961 P)). Qed.
Lemma lem4872377 {_111961 : Type'} (P : type686 _111961) : (term4 _111961 P) = (term4 _111961 P).
Proof. exact (eq_refl (term4 _111961 P)). Qed.
Lemma lem4872378 {_111961 : Type'} (P : type686 _111961) : (term74 _111961 P) = (term45 _111961 P).
Proof. exact (MK_COMB (@lem4872376 _111961 P) (@lem4872377 _111961 P)). Qed.
Lemma lem4872379 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4872380 {_111961 : Type'} (P : type686 _111961) : (term80 _111961 P) = (term81 _111961 P).
Proof. exact (MK_COMB (@lem4872379) (@lem4872378 _111961 P)). Qed.
Lemma lem4872381 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (term76 _111961 P s) = (term31 _111961 P s).
Proof. exact (eq_refl (term76 _111961 P s)). Qed.
Lemma lem4872382 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4872383 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (term82 _111961 P s) = (term83 _111961 P s).
Proof. exact (MK_COMB (@lem4872382) (@lem4872381 _111961 P s)). Qed.
Lemma lem4872384 {_111961 : Type'} (P : type686 _111961) : (term4 _111961 P) = (term4 _111961 P).
Proof. exact (eq_refl (term4 _111961 P)). Qed.
Lemma lem4872385 {_111961 : Type'} (s : _111961 -> Prop) (P : type686 _111961) : (term84 _111961 s P) = (term85 _111961 s P).
Proof. exact (MK_COMB (@lem4872383 _111961 P s) (@lem4872384 _111961 P)). Qed.
Lemma lem4872386 {_111961 : Type'} (P : type686 _111961) : (term86 _111961 P) = (term87 _111961 P).
Proof. exact (fun_ext (fun s : _111961 -> Prop => @lem4872385 _111961 s P)). Qed.
Lemma lem4872387 {_111961 : Type'} : (@ex (_111961 -> Prop)) = (@ex (_111961 -> Prop)).
Proof. exact (eq_refl (@ex (_111961 -> Prop))). Qed.
Lemma lem4872388 {_111961 : Type'} (P : type686 _111961) : (term75 _111961 P) = (term88 _111961 P).
Proof. exact (MK_COMB (@lem4872387 _111961) (@lem4872386 _111961 P)). Qed.
Lemma lem4872389 {_111961 : Type'} (P : type686 _111961) : ((term74 _111961 P) = (term75 _111961 P)) = ((term45 _111961 P) = (term88 _111961 P)).
Proof. exact (MK_COMB (@lem4872380 _111961 P) (@lem4872388 _111961 P)). Qed.
Lemma lem4872390 {_111961 : Type'} (P : type686 _111961) : (term45 _111961 P) = (term88 _111961 P).
Proof. exact (EQ_MP (@lem4872389 _111961 P) (@lem4872370 _111961 P)). Qed.
Lemma lem4872391 {_111961 : Type'} (P : type686 _111961) : (term52 _111961 P) = (term89 _111961 P).
Proof. exact (MK_COMB (@lem4872366 _111961 P) (@lem4872390 _111961 P)). Qed.
Lemma lem4872393 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4872394 {_111961 : Type'} (P : type686 _111961) (Q : type686 _111961) : (term92 _111961 P Q) = (term93 _111961 P Q).
Proof. exact (@lem4872393 (_111961 -> Prop) P Q). Qed.
Lemma lem4872395 {_111961 : Type'} (P : type686 _111961) : (term94 _111961 P) = (term95 _111961 P).
Proof. exact (@lem4872394 _111961 (term67 _111961 P) (term87 _111961 P)). Qed.
Lemma lem4872396 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (term96 _111961 P s) = (term65 _111961 P s).
Proof. exact (eq_refl (term96 _111961 P s)). Qed.
Lemma lem4872397 {_111961 : Type'} (P : type686 _111961) : (term97 _111961 P) = (term67 _111961 P).
Proof. exact (fun_ext (fun s : _111961 -> Prop => @lem4872396 _111961 P s)). Qed.
Lemma lem4872398 {_111961 : Type'} : (@ex (_111961 -> Prop)) = (@ex (_111961 -> Prop)).
Proof. exact (eq_refl (@ex (_111961 -> Prop))). Qed.
Lemma lem4872399 {_111961 : Type'} (P : type686 _111961) : (term98 _111961 P) = (term68 _111961 P).
Proof. exact (MK_COMB (@lem4872398 _111961) (@lem4872397 _111961 P)). Qed.
Lemma lem4872400 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4872401 {_111961 : Type'} (P : type686 _111961) : (term99 _111961 P) = (term69 _111961 P).
Proof. exact (MK_COMB (@lem4872400) (@lem4872399 _111961 P)). Qed.
Lemma lem4872402 {_111961 : Type'} (s : _111961 -> Prop) (P : type686 _111961) : (term100 _111961 P s) = (term85 _111961 s P).
Proof. exact (eq_refl (term100 _111961 P s)). Qed.
Lemma lem4872403 {_111961 : Type'} (P : type686 _111961) : (term101 _111961 P) = (term87 _111961 P).
Proof. exact (fun_ext (fun s : _111961 -> Prop => @lem4872402 _111961 s P)). Qed.
Lemma lem4872404 {_111961 : Type'} : (@ex (_111961 -> Prop)) = (@ex (_111961 -> Prop)).
Proof. exact (eq_refl (@ex (_111961 -> Prop))). Qed.
Lemma lem4872405 {_111961 : Type'} (P : type686 _111961) : (term102 _111961 P) = (term88 _111961 P).
Proof. exact (MK_COMB (@lem4872404 _111961) (@lem4872403 _111961 P)). Qed.
Lemma lem4872406 {_111961 : Type'} (P : type686 _111961) : (term94 _111961 P) = (term89 _111961 P).
Proof. exact (MK_COMB (@lem4872401 _111961 P) (@lem4872405 _111961 P)). Qed.
Lemma lem4872407 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4872408 {_111961 : Type'} (P : type686 _111961) : (term103 _111961 P) = (term104 _111961 P).
Proof. exact (MK_COMB (@lem4872407) (@lem4872406 _111961 P)). Qed.
Lemma lem4872409 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (term96 _111961 P s) = (term65 _111961 P s).
Proof. exact (eq_refl (term96 _111961 P s)). Qed.
Lemma lem4872410 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4872411 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (term105 _111961 P s) = (term106 _111961 P s).
Proof. exact (MK_COMB (@lem4872410) (@lem4872409 _111961 P s)). Qed.
Lemma lem4872412 {_111961 : Type'} (s : _111961 -> Prop) (P : type686 _111961) : (term100 _111961 P s) = (term85 _111961 s P).
Proof. exact (eq_refl (term100 _111961 P s)). Qed.
Lemma lem4872413 {_111961 : Type'} (s : _111961 -> Prop) (P : type686 _111961) : (term107 _111961 P s) = (term108 _111961 s P).
Proof. exact (MK_COMB (@lem4872411 _111961 P s) (@lem4872412 _111961 s P)). Qed.
Lemma lem4872414 {_111961 : Type'} (P : type686 _111961) : (term109 _111961 P) = (term110 _111961 P).
Proof. exact (fun_ext (fun s : _111961 -> Prop => @lem4872413 _111961 s P)). Qed.
Lemma lem4872415 {_111961 : Type'} : (@ex (_111961 -> Prop)) = (@ex (_111961 -> Prop)).
Proof. exact (eq_refl (@ex (_111961 -> Prop))). Qed.
Lemma lem4872416 {_111961 : Type'} (P : type686 _111961) : (term95 _111961 P) = (term111 _111961 P).
Proof. exact (MK_COMB (@lem4872415 _111961) (@lem4872414 _111961 P)). Qed.
Lemma lem4872417 {_111961 : Type'} (P : type686 _111961) : ((term94 _111961 P) = (term95 _111961 P)) = ((term89 _111961 P) = (term111 _111961 P)).
Proof. exact (MK_COMB (@lem4872408 _111961 P) (@lem4872416 _111961 P)). Qed.
Lemma lem4872418 {_111961 : Type'} (P : type686 _111961) : (term89 _111961 P) = (term111 _111961 P).
Proof. exact (EQ_MP (@lem4872417 _111961 P) (@lem4872395 _111961 P)). Qed.
Lemma lem4872420 {_111961 : Type'} (P : type686 _111961) : (term52 _111961 P) = (term111 _111961 P).
Proof. exact (TRANS (@lem4872391 _111961 P) (@lem4872418 _111961 P)). Qed.
Lemma lem4872421 {_111961 : Type'} (P : type686 _111961) : (term6 _111961 P) = (term111 _111961 P).
Proof. exact (TRANS (@lem4872327 _111961 P) (@lem4872420 _111961 P)). Qed.
Lemma lem4872422 {_111961 : Type'} (P : type686 _111961) (h1 : term6 _111961 P) : term111 _111961 P.
Proof. exact (EQ_MP (@lem4872421 _111961 P) (@lem4872285 _111961 P h1)). Qed.
Lemma lem4872423 {_111961 : Type'} (s : _111961 -> Prop) : ((term1 _111961 s) = s) = ((term1 _111961 s) = s).
Proof. exact (eq_refl ((term1 _111961 s) = s)). Qed.
Lemma lem4872424 {_111961 : Type'} : (term20 _111961) = (term20 _111961).
Proof. exact (fun_ext (fun s : _111961 -> Prop => @lem4872423 _111961 s)). Qed.
Lemma lem4872425 {_111961 : Type'} : (@all (_111961 -> Prop)) = (@all (_111961 -> Prop)).
Proof. exact (eq_refl (@all (_111961 -> Prop))). Qed.
Lemma lem4872434 {_111961 : Type'} : (term7 _111961) = (term7 _111961).
Proof. exact (MK_COMB (@lem4872425 _111961) (@lem4872424 _111961)). Qed.
Lemma lem4872435 {_111961 : Type'} (h1 : term7 _111961) : term7 _111961.
Proof. exact (EQ_MP (@lem4872434 _111961) (@lem4872286 _111961 h1)). Qed.
Lemma lem4872436 {_111961 : Type'} (s : _111961 -> Prop) (P : type686 _111961) (h1 : term108 _111961 s P) : term108 _111961 s P.
Proof. exact (h1). Qed.
Lemma lem4872449 {_111961 : Type'} (s : _111961 -> Prop) : ((term1 _111961 s) = s) = ((term1 _111961 s) = s).
Proof. exact (eq_refl ((term1 _111961 s) = s)). Qed.
Lemma lem4872450 {_111961 : Type'} : (term20 _111961) = (term20 _111961).
Proof. exact (fun_ext (fun s : _111961 -> Prop => @lem4872449 _111961 s)). Qed.
Lemma lem4872451 {_111961 : Type'} : (@all (_111961 -> Prop)) = (@all (_111961 -> Prop)).
Proof. exact (eq_refl (@all (_111961 -> Prop))). Qed.
Lemma lem4872452 {_111961 : Type'} : (term7 _111961) = (term7 _111961).
Proof. exact (MK_COMB (@lem4872451 _111961) (@lem4872450 _111961)). Qed.
Lemma lem4872453 {_111961 : Type'} (h1 : term7 _111961) : term7 _111961.
Proof. exact (EQ_MP (@lem4872452 _111961) (@lem4872435 _111961 h1)). Qed.
Lemma lem4872456 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem4872457 {_111961 : Type'} (P : type686 _111961) : (term21 _111961 P) = (term21 _111961 P).
Proof. exact (fun_ext (fun s : _111961 -> Prop => @lem4872456 _111961 P s)). Qed.
Lemma lem4872458 {_111961 : Type'} : (@all (_111961 -> Prop)) = (@all (_111961 -> Prop)).
Proof. exact (eq_refl (@all (_111961 -> Prop))). Qed.
Lemma lem4872459 {_111961 : Type'} (P : type686 _111961) : (term4 _111961 P) = (term4 _111961 P).
Proof. exact (MK_COMB (@lem4872458 _111961) (@lem4872457 _111961 P)). Qed.
Lemma lem4872470 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (term83 _111961 P s) = (term83 _111961 P s).
Proof. exact (eq_refl (term83 _111961 P s)). Qed.
Lemma lem4872471 {_111961 : Type'} (s : _111961 -> Prop) (P : type686 _111961) : (term85 _111961 s P) = (term85 _111961 s P).
Proof. exact (MK_COMB (@lem4872470 _111961 P s) (@lem4872459 _111961 P)). Qed.
Lemma lem4872476 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (term39 _111961 P s) = (term39 _111961 P s).
Proof. exact (eq_refl (term39 _111961 P s)). Qed.
Lemma lem4872483 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (term22 _111961 P s) = (term22 _111961 P s).
Proof. exact (eq_refl (term22 _111961 P s)). Qed.
Lemma lem4872484 {_111961 : Type'} (P : type686 _111961) : (term23 _111961 P) = (term23 _111961 P).
Proof. exact (fun_ext (fun s : _111961 -> Prop => @lem4872483 _111961 P s)). Qed.
Lemma lem4872485 {_111961 : Type'} : (@all (_111961 -> Prop)) = (@all (_111961 -> Prop)).
Proof. exact (eq_refl (@all (_111961 -> Prop))). Qed.
Lemma lem4872486 {_111961 : Type'} (P : type686 _111961) : (term3 _111961 P) = (term3 _111961 P).
Proof. exact (MK_COMB (@lem4872485 _111961) (@lem4872484 _111961 P)). Qed.
Lemma lem4872487 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4872488 {_111961 : Type'} (P : type686 _111961) : (term46 _111961 P) = (term46 _111961 P).
Proof. exact (MK_COMB (@lem4872487) (@lem4872486 _111961 P)). Qed.
Lemma lem4872489 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (term65 _111961 P s) = (term65 _111961 P s).
Proof. exact (MK_COMB (@lem4872488 _111961 P) (@lem4872476 _111961 P s)). Qed.
Lemma lem4872490 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4872491 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (term106 _111961 P s) = (term106 _111961 P s).
Proof. exact (MK_COMB (@lem4872490) (@lem4872489 _111961 P s)). Qed.
Lemma lem4872492 {_111961 : Type'} (s : _111961 -> Prop) (P : type686 _111961) : (term108 _111961 s P) = (term108 _111961 s P).
Proof. exact (MK_COMB (@lem4872491 _111961 P s) (@lem4872471 _111961 s P)). Qed.
Lemma lem4872493 {_111961 : Type'} (s : _111961 -> Prop) (P : type686 _111961) (h1 : term108 _111961 s P) : term108 _111961 s P.
Proof. exact (EQ_MP (@lem4872492 _111961 s P) (@lem4872436 _111961 s P h1)). Qed.
Lemma lem4872494 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) (h1 : term65 _111961 P s) : term65 _111961 P s.
Proof. exact (h1). Qed.
Lemma lem4872495 {_111961 : Type'} (s : _111961 -> Prop) (P : type686 _111961) (h1 : term85 _111961 s P) : term85 _111961 s P.
Proof. exact (h1). Qed.
Lemma lem4872497 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) (h1 : term65 _111961 P s) : term3 _111961 P.
Proof. exact (proj1 (@lem4872494 _111961 P s h1)). Qed.
Lemma lem4872498 {_111961 : Type'} (s : _111961 -> Prop) (P : type686 _111961) (h1 : term85 _111961 s P) : term4 _111961 P.
Proof. exact (proj2 (@lem4872495 _111961 s P h1)). Qed.
Lemma lem4872501 {_111961 : Type'} (s : _111961 -> Prop) : ((term1 _111961 s) = s) = ((term1 _111961 s) = s).
Proof. exact (eq_refl ((term1 _111961 s) = s)). Qed.
Lemma lem4872502 {_111961 : Type'} : (term20 _111961) = (term20 _111961).
Proof. exact (fun_ext (fun s : _111961 -> Prop => @lem4872501 _111961 s)). Qed.
Lemma lem4872503 {_111961 : Type'} : (@all (_111961 -> Prop)) = (@all (_111961 -> Prop)).
Proof. exact (eq_refl (@all (_111961 -> Prop))). Qed.
Lemma lem4872505 {_111961 : Type'} : (term7 _111961) = (term7 _111961).
Proof. exact (MK_COMB (@lem4872503 _111961) (@lem4872502 _111961)). Qed.
Lemma lem4872506 {_111961 : Type'} (h1 : term7 _111961) : term7 _111961.
Proof. exact (EQ_MP (@lem4872505 _111961) (@lem4872453 _111961 h1)). Qed.
Lemma lem4872508 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (term22 _111961 P s) = (term22 _111961 P s).
Proof. exact (eq_refl (term22 _111961 P s)). Qed.
Lemma lem4872509 {_111961 : Type'} (P : type686 _111961) : (term23 _111961 P) = (term23 _111961 P).
Proof. exact (fun_ext (fun s : _111961 -> Prop => @lem4872508 _111961 P s)). Qed.
Lemma lem4872510 {_111961 : Type'} : (@all (_111961 -> Prop)) = (@all (_111961 -> Prop)).
Proof. exact (eq_refl (@all (_111961 -> Prop))). Qed.
Lemma lem4872512 {_111961 : Type'} (P : type686 _111961) : (term3 _111961 P) = (term3 _111961 P).
Proof. exact (MK_COMB (@lem4872510 _111961) (@lem4872509 _111961 P)). Qed.
Lemma lem4872513 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) (h1 : term65 _111961 P s) : term3 _111961 P.
Proof. exact (EQ_MP (@lem4872512 _111961 P) (@lem4872497 _111961 P s h1)). Qed.
Lemma lem4872530 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem4872531 {_111961 : Type'} (P : type686 _111961) : (term21 _111961 P) = (term21 _111961 P).
Proof. exact (fun_ext (fun s : _111961 -> Prop => @lem4872530 _111961 P s)). Qed.
Lemma lem4872532 {_111961 : Type'} : (@all (_111961 -> Prop)) = (@all (_111961 -> Prop)).
Proof. exact (eq_refl (@all (_111961 -> Prop))). Qed.
Lemma lem4872534 {_111961 : Type'} (P : type686 _111961) : (term4 _111961 P) = (term4 _111961 P).
Proof. exact (MK_COMB (@lem4872532 _111961) (@lem4872531 _111961 P)). Qed.
Lemma lem4872535 {_111961 : Type'} (s : _111961 -> Prop) (P : type686 _111961) (h1 : term85 _111961 s P) : term4 _111961 P.
Proof. exact (EQ_MP (@lem4872534 _111961 P) (@lem4872498 _111961 s P h1)). Qed.
Lemma lem4872536 {_111961 : Type'} (_60267 : _111961 -> Prop) (h1 : term7 _111961) : term0 _111961 _60267.
Proof. exact (@lem4872506 _111961 h1 _60267). Qed.
Lemma lem4872537 {_111961 : Type'} (_60267 : _111961 -> Prop) : (term0 _111961 _60267) = ((term1 _111961 _60267) = _60267).
Proof. exact (eq_refl (term0 _111961 _60267)). Qed.
Lemma lem4872539 {_111961 : Type'} (_60268 : _111961 -> Prop) (P : type686 _111961) (s : _111961 -> Prop) (h1 : term65 _111961 P s) : term29 _111961 P _60268.
Proof. exact (@lem4872513 _111961 P s h1 _60268). Qed.
Lemma lem4872540 {_111961 : Type'} (P : type686 _111961) (_60268 : _111961 -> Prop) : (term29 _111961 P _60268) = (term22 _111961 P _60268).
Proof. exact (eq_refl (term29 _111961 P _60268)). Qed.
Lemma lem4872545 {_111961 : Type'} (_60270 : _111961 -> Prop) (s : _111961 -> Prop) (P : type686 _111961) (h1 : term85 _111961 s P) : term37 _111961 P _60270.
Proof. exact (@lem4872535 _111961 s P h1 _60270). Qed.
Lemma lem4872546 {_111961 : Type'} (P : type686 _111961) (_60270 : _111961 -> Prop) : (term37 _111961 P _60270) = (P _60270).
Proof. exact (eq_refl (term37 _111961 P _60270)). Qed.
Lemma lem4872553 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) (h1 : term65 _111961 P s) : term39 _111961 P s.
Proof. exact (proj2 (@lem4872494 _111961 P s h1)). Qed.
Lemma lem4872557 {_111961 : Type'} (s : _111961 -> Prop) (P : type686 _111961) (h1 : term85 _111961 s P) : term31 _111961 P s.
Proof. exact (proj1 (@lem4872495 _111961 s P h1)). Qed.
Lemma lem4872560 {_111961 : Type'} (P : type686 _111961) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4872561 {_111961 : Type'} (_60271 : _111961 -> Prop) (_60272 : _111961 -> Prop) (h1 : _60271 = _60272) : _60271 = _60272.
Proof. exact (h1). Qed.
Lemma lem4872562 {_111961 : Type'} (P : type686 _111961) (_60271 : _111961 -> Prop) (_60272 : _111961 -> Prop) (h1 : _60271 = _60272) : (P _60271) = (P _60272).
Proof. exact (MK_COMB (@lem4872560 _111961 P) (@lem4872561 _111961 _60271 _60272 h1)). Qed.
Lemma lem4872564 (b : Prop) (a : Prop) : term112 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem4872565 {_111961 : Type'} (_60272 : _111961 -> Prop) (P : type686 _111961) (_60271 : _111961 -> Prop) : term113 _111961 _60272 P _60271.
Proof. exact (@lem4872564 (P _60272) (P _60271)). Qed.
Lemma lem4872566 {_111961 : Type'} (P : type686 _111961) (_60271 : _111961 -> Prop) (_60272 : _111961 -> Prop) (h1 : _60271 = _60272) : term114 _111961 _60272 P _60271.
Proof. exact (@lem4872565 _111961 _60272 P _60271 (@lem4872562 _111961 P _60271 _60272 h1)). Qed.
Lemma lem4872567 {_111961 : Type'} (_60272 : _111961 -> Prop) (P : type686 _111961) (_60271 : _111961 -> Prop) : term115 _111961 _60272 P _60271.
Proof. exact (fun h0 : _60271 = _60272 => @lem4872566 _111961 P _60271 _60272 h0). Qed.
Lemma lem4872569 (a : Prop) (b : Prop) : (a -> b) = (term116 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4872570 {_111961 : Type'} (_60272 : _111961 -> Prop) (P : type686 _111961) (_60271 : _111961 -> Prop) : (term115 _111961 _60272 P _60271) = (term117 _111961 _60272 P _60271).
Proof. exact (@lem4872569 (_60271 = _60272) (term114 _111961 _60272 P _60271)). Qed.
Lemma lem4872571 {_111961 : Type'} (_60272 : _111961 -> Prop) (P : type686 _111961) (_60271 : _111961 -> Prop) : term117 _111961 _60272 P _60271.
Proof. exact (EQ_MP (@lem4872570 _111961 _60272 P _60271) (@lem4872567 _111961 _60272 P _60271)). Qed.
Lemma lem4872590 {_111961 : Type'} (_60267 : _111961 -> Prop) (h1 : term7 _111961) : (term1 _111961 _60267) = _60267.
Proof. exact (EQ_MP (@lem4872537 _111961 _60267) (@lem4872536 _111961 _60267 h1)). Qed.
Lemma lem4872591 {_111961 : Type'} (_60267 : _111961 -> Prop) (h1 : term7 _111961) : (term1 _111961 _60267) = _60267.
Proof. exact (@lem4872590 _111961 _60267 h1). Qed.
Lemma lem4872592 {_111961 : Type'} (s : _111961 -> Prop) (h1 : term7 _111961) : (term1 _111961 s) = s.
Proof. exact (@lem4872591 _111961 s h1). Qed.
Lemma lem4872593 {_111961 : Type'} (s : _111961 -> Prop) (h1 : term7 _111961) : term118 _111961 s.
Proof. exact (fun h0 : term119 _111961 s => @lem4872592 _111961 s h1). Qed.
Lemma lem4872595 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4872596 {_111961 : Type'} (s : _111961 -> Prop) : (term118 _111961 s) = ((term1 _111961 s) = s).
Proof. exact (@lem4872595 ((term1 _111961 s) = s)). Qed.
Lemma lem4872597 {_111961 : Type'} (s : _111961 -> Prop) (h1 : term7 _111961) : (term1 _111961 s) = s.
Proof. exact (EQ_MP (@lem4872596 _111961 s) (@lem4872593 _111961 s h1)). Qed.
Lemma lem4872599 {_111961 : Type'} (_60268 : _111961 -> Prop) (P : type686 _111961) (s : _111961 -> Prop) (h1 : term65 _111961 P s) : term22 _111961 P _60268.
Proof. exact (EQ_MP (@lem4872540 _111961 P _60268) (@lem4872539 _111961 _60268 P s h1)). Qed.
Lemma lem4872600 {_111961 : Type'} (_60268 : _111961 -> Prop) (P : type686 _111961) (s : _111961 -> Prop) (h1 : term65 _111961 P s) : term22 _111961 P _60268.
Proof. exact (@lem4872599 _111961 _60268 P s h1). Qed.
Lemma lem4872601 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) (h1 : term65 _111961 P s) : term121 _111961 P s.
Proof. exact (@lem4872600 _111961 (@DIFF _111961 (@UNIV _111961) s) P s h1). Qed.
Lemma lem4872602 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) (h1 : term65 _111961 P s) : term122 _111961 P s.
Proof. exact (fun h0 : term123 _111961 P s => @lem4872601 _111961 P s h1). Qed.
Lemma lem4872604 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4872605 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (term122 _111961 P s) = (term121 _111961 P s).
Proof. exact (@lem4872604 (term121 _111961 P s)). Qed.
Lemma lem4872606 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) (h1 : term65 _111961 P s) : term121 _111961 P s.
Proof. exact (EQ_MP (@lem4872605 _111961 P s) (@lem4872602 _111961 P s h1)). Qed.
Lemma lem4872612 (q : Prop) (p : Prop) (r : Prop) : (term124 p q r) = (term124 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4872613 {_111961 : Type'} (_60272 : _111961 -> Prop) (P : type686 _111961) (_60271 : _111961 -> Prop) : (term117 _111961 _60272 P _60271) = (term125 _111961 _60272 P _60271).
Proof. exact (@lem4872612 (P _60272) (term126 _111961 _60271 _60272) (term39 _111961 P _60271)). Qed.
Lemma lem4872627 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4872628 {_111961 : Type'} (P : type686 _111961) (_60271 : _111961 -> Prop) (_60272 : _111961 -> Prop) : (term127 _111961 _60272 P _60271) = (term128 _111961 P _60271 _60272).
Proof. exact (@lem4872627 (term39 _111961 P _60271) (term126 _111961 _60271 _60272)). Qed.
Lemma lem4872636 {_111961 : Type'} (P : type686 _111961) (_60272 : _111961 -> Prop) : (term129 _111961 P _60272) = (term129 _111961 P _60272).
Proof. exact (eq_refl (term129 _111961 P _60272)). Qed.
Lemma lem4872637 {_111961 : Type'} (P : type686 _111961) (_60271 : _111961 -> Prop) (_60272 : _111961 -> Prop) : (term125 _111961 _60272 P _60271) = (term130 _111961 P _60271 _60272).
Proof. exact (MK_COMB (@lem4872636 _111961 P _60272) (@lem4872628 _111961 P _60271 _60272)). Qed.
Lemma lem4872648 {_111961 : Type'} (P : type686 _111961) (_60271 : _111961 -> Prop) (_60272 : _111961 -> Prop) : (term117 _111961 _60272 P _60271) = (term130 _111961 P _60271 _60272).
Proof. exact (TRANS (@lem4872613 _111961 _60272 P _60271) (@lem4872637 _111961 P _60271 _60272)). Qed.
Lemma lem4872649 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4872650 {_111961 : Type'} (P : type686 _111961) (_60271 : _111961 -> Prop) (_60272 : _111961 -> Prop) : (term131 _111961 _60272 P _60271) = (term132 _111961 P _60271 _60272).
Proof. exact (MK_COMB (@lem4872649) (@lem4872648 _111961 P _60271 _60272)). Qed.
Lemma lem4872664 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4872665 {_111961 : Type'} (P : type686 _111961) (_60271 : _111961 -> Prop) (_60272 : _111961 -> Prop) : (term127 _111961 _60272 P _60271) = (term128 _111961 P _60271 _60272).
Proof. exact (@lem4872664 (term39 _111961 P _60271) (term126 _111961 _60271 _60272)). Qed.
Lemma lem4872673 {_111961 : Type'} (P : type686 _111961) (_60272 : _111961 -> Prop) : (term129 _111961 P _60272) = (term129 _111961 P _60272).
Proof. exact (eq_refl (term129 _111961 P _60272)). Qed.
Lemma lem4872674 {_111961 : Type'} (P : type686 _111961) (_60271 : _111961 -> Prop) (_60272 : _111961 -> Prop) : (term125 _111961 _60272 P _60271) = (term130 _111961 P _60271 _60272).
Proof. exact (MK_COMB (@lem4872673 _111961 P _60272) (@lem4872665 _111961 P _60271 _60272)). Qed.
Lemma lem4872685 {_111961 : Type'} (P : type686 _111961) (_60271 : _111961 -> Prop) (_60272 : _111961 -> Prop) : ((term117 _111961 _60272 P _60271) = (term125 _111961 _60272 P _60271)) = ((term130 _111961 P _60271 _60272) = (term130 _111961 P _60271 _60272)).
Proof. exact (MK_COMB (@lem4872650 _111961 P _60271 _60272) (@lem4872674 _111961 P _60271 _60272)). Qed.
Lemma lem4872687 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4872688 (x : Prop) : (x = x) = True.
Proof. exact (@lem4872687 Prop x). Qed.
Lemma lem4872689 {_111961 : Type'} (P : type686 _111961) (_60271 : _111961 -> Prop) (_60272 : _111961 -> Prop) : ((term130 _111961 P _60271 _60272) = (term130 _111961 P _60271 _60272)) = True.
Proof. exact (@lem4872688 (term130 _111961 P _60271 _60272)). Qed.
Lemma lem4872690 {_111961 : Type'} (_60272 : _111961 -> Prop) (P : type686 _111961) (_60271 : _111961 -> Prop) : ((term117 _111961 _60272 P _60271) = (term125 _111961 _60272 P _60271)) = True.
Proof. exact (TRANS (@lem4872685 _111961 P _60271 _60272) (@lem4872689 _111961 P _60271 _60272)). Qed.
Lemma lem4872691 {_111961 : Type'} (_60272 : _111961 -> Prop) (P : type686 _111961) (_60271 : _111961 -> Prop) : True = ((term117 _111961 _60272 P _60271) = (term125 _111961 _60272 P _60271)).
Proof. exact (SYM (@lem4872690 _111961 _60272 P _60271)). Qed.
Lemma lem4872692 {_111961 : Type'} (_60272 : _111961 -> Prop) (P : type686 _111961) (_60271 : _111961 -> Prop) : (term117 _111961 _60272 P _60271) = (term125 _111961 _60272 P _60271).
Proof. exact (EQ_MP (@lem4872691 _111961 _60272 P _60271) (@lem0)). Qed.
Lemma lem4872693 {_111961 : Type'} (_60272 : _111961 -> Prop) (P : type686 _111961) (_60271 : _111961 -> Prop) : term125 _111961 _60272 P _60271.
Proof. exact (EQ_MP (@lem4872692 _111961 _60272 P _60271) (@lem4872571 _111961 _60272 P _60271)). Qed.
Lemma lem4872695 (b : Prop) (a : Prop) : (a \/ b) = (term133 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4872696 {_111961 : Type'} (_60271 : _111961 -> Prop) (P : type686 _111961) (_60272 : _111961 -> Prop) : (term125 _111961 _60272 P _60271) = (term134 _111961 _60271 P _60272).
Proof. exact (@lem4872695 (term127 _111961 _60272 P _60271) (P _60272)). Qed.
Lemma lem4872698 (a : Prop) (b : Prop) : (term135 a b) = (term136 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4872699 {_111961 : Type'} (_60272 : _111961 -> Prop) (P : type686 _111961) (_60271 : _111961 -> Prop) : (term137 _111961 _60272 P _60271) = (term138 _111961 _60272 P _60271).
Proof. exact (@lem4872698 (term126 _111961 _60271 _60272) (term39 _111961 P _60271)). Qed.
Lemma lem4872701 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4872702 {_111961 : Type'} (_60271 : _111961 -> Prop) (_60272 : _111961 -> Prop) : (term140 _111961 _60271 _60272) = (_60271 = _60272).
Proof. exact (@lem4872701 (_60271 = _60272)). Qed.
Lemma lem4872703 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4872704 {_111961 : Type'} (_60271 : _111961 -> Prop) (_60272 : _111961 -> Prop) : (term141 _111961 _60271 _60272) = (term142 _111961 _60271 _60272).
Proof. exact (MK_COMB (@lem4872703) (@lem4872702 _111961 _60271 _60272)). Qed.
Lemma lem4872706 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4872707 {_111961 : Type'} (P : type686 _111961) (_60271 : _111961 -> Prop) : (term143 _111961 P _60271) = (P _60271).
Proof. exact (@lem4872706 (P _60271)). Qed.
Lemma lem4872708 {_111961 : Type'} (_60272 : _111961 -> Prop) (P : type686 _111961) (_60271 : _111961 -> Prop) : (term138 _111961 _60272 P _60271) = (term144 _111961 _60272 P _60271).
Proof. exact (MK_COMB (@lem4872704 _111961 _60271 _60272) (@lem4872707 _111961 P _60271)). Qed.
Lemma lem4872709 {_111961 : Type'} (_60272 : _111961 -> Prop) (P : type686 _111961) (_60271 : _111961 -> Prop) : (term137 _111961 _60272 P _60271) = (term144 _111961 _60272 P _60271).
Proof. exact (TRANS (@lem4872699 _111961 _60272 P _60271) (@lem4872708 _111961 _60272 P _60271)). Qed.
Lemma lem4872710 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4872711 {_111961 : Type'} (_60272 : _111961 -> Prop) (P : type686 _111961) (_60271 : _111961 -> Prop) : (term145 _111961 _60272 P _60271) = (term146 _111961 _60272 P _60271).
Proof. exact (MK_COMB (@lem4872710) (@lem4872709 _111961 _60272 P _60271)). Qed.
Lemma lem4872712 {_111961 : Type'} (P : type686 _111961) (_60272 : _111961 -> Prop) : (P _60272) = (P _60272).
Proof. exact (eq_refl (P _60272)). Qed.
Lemma lem4872713 {_111961 : Type'} (_60271 : _111961 -> Prop) (P : type686 _111961) (_60272 : _111961 -> Prop) : (term134 _111961 _60271 P _60272) = (term147 _111961 _60271 P _60272).
Proof. exact (MK_COMB (@lem4872711 _111961 _60272 P _60271) (@lem4872712 _111961 P _60272)). Qed.
Lemma lem4872714 {_111961 : Type'} (_60271 : _111961 -> Prop) (P : type686 _111961) (_60272 : _111961 -> Prop) : (term125 _111961 _60272 P _60271) = (term147 _111961 _60271 P _60272).
Proof. exact (TRANS (@lem4872696 _111961 _60271 P _60272) (@lem4872713 _111961 _60271 P _60272)). Qed.
Lemma lem4872716 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) (h1 : term7 _111961) (h2 : term65 _111961 P s) : term148 _111961 P s.
Proof. exact (conj (@lem4872597 _111961 s h1) (@lem4872606 _111961 P s h2)). Qed.
Lemma lem4872718 {_111961 : Type'} (_60271 : _111961 -> Prop) (P : type686 _111961) (_60272 : _111961 -> Prop) : term147 _111961 _60271 P _60272.
Proof. exact (EQ_MP (@lem4872714 _111961 _60271 P _60272) (@lem4872693 _111961 _60272 P _60271)). Qed.
Lemma lem4872719 {_111961 : Type'} (_60271 : _111961 -> Prop) (P : type686 _111961) (_60272 : _111961 -> Prop) : term147 _111961 _60271 P _60272.
Proof. exact (@lem4872718 _111961 _60271 P _60272). Qed.
Lemma lem4872720 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : term149 _111961 P s.
Proof. exact (@lem4872719 _111961 (term1 _111961 s) P s). Qed.
Lemma lem4872723 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) (h1 : term7 _111961) (h2 : term65 _111961 P s) : P s.
Proof. exact (@lem4872720 _111961 P s (@lem4872716 _111961 P s h1 h2)). Qed.
Lemma lem4872724 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) (h1 : term7 _111961) (h2 : term65 _111961 P s) : term150 _111961 P s.
Proof. exact (fun h0 : term39 _111961 P s => @lem4872723 _111961 P s h1 h2). Qed.
Lemma lem4872726 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4872727 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (term150 _111961 P s) = (P s).
Proof. exact (@lem4872726 (P s)). Qed.
Lemma lem4872728 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) (h1 : term7 _111961) (h2 : term65 _111961 P s) : P s.
Proof. exact (EQ_MP (@lem4872727 _111961 P s) (@lem4872724 _111961 P s h1 h2)). Qed.
Lemma lem4872731 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4872733 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (term39 _111961 P s) = (term151 _111961 P s).
Proof. exact (@lem4872731 (P s)). Qed.
Lemma lem4872736 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) (h1 : term65 _111961 P s) : term151 _111961 P s.
Proof. exact (EQ_MP (@lem4872733 _111961 P s) (@lem4872553 _111961 P s h1)). Qed.
Lemma lem4872739 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) (h1 : term7 _111961) (h2 : term65 _111961 P s) : False.
Proof. exact (@lem4872736 _111961 P s h2 (@lem4872728 _111961 P s h1 h2)). Qed.
Lemma lem4872740 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) (h1 : term7 _111961) (h2 : term65 _111961 P s) : term152.
Proof. exact (fun h0 : ~ False => @lem4872739 _111961 P s h1 h2). Qed.
Lemma lem4872742 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4872743 : term152 = False.
Proof. exact (@lem4872742 False). Qed.
Lemma lem4872744 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) (h1 : term7 _111961) (h2 : term65 _111961 P s) : False.
Proof. exact (EQ_MP (@lem4872743) (@lem4872740 _111961 P s h1 h2)). Qed.
Lemma lem4872775 {_111961 : Type'} (_60270 : _111961 -> Prop) (s : _111961 -> Prop) (P : type686 _111961) (h1 : term85 _111961 s P) : P _60270.
Proof. exact (EQ_MP (@lem4872546 _111961 P _60270) (@lem4872545 _111961 _60270 s P h1)). Qed.
Lemma lem4872776 {_111961 : Type'} (_60270 : _111961 -> Prop) (s : _111961 -> Prop) (P : type686 _111961) (h1 : term85 _111961 s P) : P _60270.
Proof. exact (@lem4872775 _111961 _60270 s P h1). Qed.
Lemma lem4872777 {_111961 : Type'} (s : _111961 -> Prop) (P : type686 _111961) (h1 : term85 _111961 s P) : term22 _111961 P s.
Proof. exact (@lem4872776 _111961 (@DIFF _111961 (@UNIV _111961) s) s P h1). Qed.
Lemma lem4872778 {_111961 : Type'} (s : _111961 -> Prop) (P : type686 _111961) (h1 : term85 _111961 s P) : term153 _111961 P s.
Proof. exact (fun h0 : term31 _111961 P s => @lem4872777 _111961 s P h1). Qed.
Lemma lem4872780 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4872781 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (term153 _111961 P s) = (term22 _111961 P s).
Proof. exact (@lem4872780 (term22 _111961 P s)). Qed.
Lemma lem4872782 {_111961 : Type'} (s : _111961 -> Prop) (P : type686 _111961) (h1 : term85 _111961 s P) : term22 _111961 P s.
Proof. exact (EQ_MP (@lem4872781 _111961 P s) (@lem4872778 _111961 s P h1)). Qed.
Lemma lem4872785 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4872787 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) : (term31 _111961 P s) = (term154 _111961 P s).
Proof. exact (@lem4872785 (term22 _111961 P s)). Qed.
Lemma lem4872790 {_111961 : Type'} (s : _111961 -> Prop) (P : type686 _111961) (h1 : term85 _111961 s P) : term154 _111961 P s.
Proof. exact (EQ_MP (@lem4872787 _111961 P s) (@lem4872557 _111961 s P h1)). Qed.
Lemma lem4872793 {_111961 : Type'} (s : _111961 -> Prop) (P : type686 _111961) (h1 : term85 _111961 s P) : False.
Proof. exact (@lem4872790 _111961 s P h1 (@lem4872782 _111961 s P h1)). Qed.
Lemma lem4872794 {_111961 : Type'} (s : _111961 -> Prop) (P : type686 _111961) (h1 : term85 _111961 s P) : term152.
Proof. exact (fun h0 : ~ False => @lem4872793 _111961 s P h1). Qed.
Lemma lem4872796 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4872797 : term152 = False.
Proof. exact (@lem4872796 False). Qed.
Lemma lem4872798 {_111961 : Type'} (s : _111961 -> Prop) (P : type686 _111961) (h1 : term85 _111961 s P) : False.
Proof. exact (EQ_MP (@lem4872797) (@lem4872794 _111961 s P h1)). Qed.
Lemma lem4872799 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) (h1 : term7 _111961) (h2 : term65 _111961 P s) : (term7 _111961) = False.
Proof. exact (prop_ext (fun h3 : term7 _111961 => @lem4872744 _111961 P s h1 h2) (fun h3 : False => @lem4872506 _111961 h1)). Qed.
Lemma lem4872800 {_111961 : Type'} (P : type686 _111961) (s : _111961 -> Prop) (h1 : term7 _111961) (h2 : term65 _111961 P s) : False.
Proof. exact (EQ_MP (@lem4872799 _111961 P s h1 h2) (@lem4872506 _111961 h1)). Qed.
Lemma lem4872801 {_111961 : Type'} (s : _111961 -> Prop) (P : type686 _111961) (h1 : term7 _111961) (h2 : term108 _111961 s P) : False.
Proof. exact (or_elim (@lem4872493 _111961 s P h2) (fun h0 : term65 _111961 P s => @lem4872800 _111961 P s h1 h0) (fun h0 : term85 _111961 s P => @lem4872798 _111961 s P h0)). Qed.
Lemma lem4872802 {_111961 : Type'} (s : _111961 -> Prop) (P : type686 _111961) (h1 : term7 _111961) (h2 : term108 _111961 s P) : (term108 _111961 s P) = False.
Proof. exact (prop_ext (fun h3 : term108 _111961 s P => @lem4872801 _111961 s P h1 h2) (fun h3 : False => @lem4872493 _111961 s P h2)). Qed.
Lemma lem4872803 {_111961 : Type'} (s : _111961 -> Prop) (P : type686 _111961) (h1 : term7 _111961) (h2 : term108 _111961 s P) : False.
Proof. exact (EQ_MP (@lem4872802 _111961 s P h1 h2) (@lem4872493 _111961 s P h2)). Qed.
Lemma lem4872804 {_111961 : Type'} (s : _111961 -> Prop) (P : type686 _111961) (h1 : term7 _111961) (h2 : term108 _111961 s P) : (term7 _111961) = False.
Proof. exact (prop_ext (fun h3 : term7 _111961 => @lem4872803 _111961 s P h1 h2) (fun h3 : False => @lem4872453 _111961 h1)). Qed.
Lemma lem4872805 {_111961 : Type'} (s : _111961 -> Prop) (P : type686 _111961) (h1 : term7 _111961) (h2 : term108 _111961 s P) : False.
Proof. exact (EQ_MP (@lem4872804 _111961 s P h1 h2) (@lem4872453 _111961 h1)). Qed.
Lemma lem4872806 {_111961 : Type'} (P : type686 _111961) (h1 : term7 _111961) (h2 : term6 _111961 P) : False.
Proof. exact (ex_elim (@lem4872422 _111961 P h2) (fun s : _111961 -> Prop => fun h0 : term110 _111961 P s => @lem4872805 _111961 s P h1 h0)). Qed.
Lemma lem4872807 {_111961 : Type'} (P : type686 _111961) (h1 : term7 _111961) (h2 : term6 _111961 P) : (term7 _111961) = False.
Proof. exact (prop_ext (fun h3 : term7 _111961 => @lem4872806 _111961 P h1 h2) (fun h3 : False => @lem4872435 _111961 h1)). Qed.
Lemma lem4872808 {_111961 : Type'} (P : type686 _111961) (h1 : term7 _111961) (h2 : term6 _111961 P) : False.
Proof. exact (EQ_MP (@lem4872807 _111961 P h1 h2) (@lem4872435 _111961 h1)). Qed.
Lemma lem4872809 {_111961 : Type'} (P : type686 _111961) (h1 : term6 _111961 P) : term12 _111961.
Proof. exact (fun h0 : term7 _111961 => @lem4872808 _111961 P h0 h1). Qed.
Lemma lem4872810 {_111961 : Type'} : (term12 _111961) = (term13 _111961).
Proof. exact (@lem69 (term7 _111961)). Qed.
Lemma lem4872811 {_111961 : Type'} (P : type686 _111961) (h1 : term6 _111961 P) : term13 _111961.
Proof. exact (EQ_MP (@lem4872810 _111961) (@lem4872809 _111961 P h1)). Qed.
Lemma lem4872812 {_111961 : Type'} (P : type686 _111961) : term15 _111961 P.
Proof. exact (fun h0 : term6 _111961 P => @lem4872811 _111961 P h0). Qed.
Lemma lem4872817 {_111961 : Type'} : term19 _111961.
Proof. exact (fun P : type686 _111961 => @lem4872812 _111961 P). Qed.
Lemma lem4872818 {_111961 : Type'} : term18 _111961.
Proof. exact (EQ_MP (@lem4872284 _111961) (@lem4872817 _111961)). Qed.
Lemma lem4872819 {_111961 : Type'} (P : type686 _111961) : term155 _111961 P.
Proof. exact (@lem4872818 _111961 P). Qed.
Lemma lem4872820 {_111961 : Type'} (P : type686 _111961) : (term155 _111961 P) = (term8 _111961 P).
Proof. exact (eq_refl (term155 _111961 P)). Qed.
Lemma lem4872821 {_111961 : Type'} (P : type686 _111961) : term8 _111961 P.
Proof. exact (EQ_MP (@lem4872820 _111961 P) (@lem4872819 _111961 P)). Qed.
Lemma lem4872823 {_111961 : Type'} (P : type686 _111961) : term8 _111961 P.
Proof. exact (@lem4872193 _111961 P (@lem4872821 _111961 P)). Qed.
Lemma lem4872824 {_111961 : Type'} (P : type686 _111961) (h1 : term6 _111961 P) : term12 _111961.
Proof. exact (@lem4872823 _111961 P (@lem4872175 _111961 P h1)). Qed.
Lemma lem4872825 {_111961 : Type'} (P : type686 _111961) (h1 : term6 _111961 P) : False.
Proof. exact (@lem4872824 _111961 P h1 (@lem4872176 _111961)). Qed.
Lemma lem4872826 {_111961 : Type'} (P : type686 _111961) (h1 : term6 _111961 P) : (term6 _111961 P) = False.
Proof. exact (prop_ext (fun h2 : term6 _111961 P => @lem4872825 _111961 P h1) (fun h2 : False => @lem4872175 _111961 P h1)). Qed.
Lemma lem4872827 {_111961 : Type'} (P : type686 _111961) (h1 : term6 _111961 P) : False.
Proof. exact (EQ_MP (@lem4872826 _111961 P h1) (@lem4872175 _111961 P h1)). Qed.
Lemma lem4872828 {_111961 : Type'} (P : type686 _111961) : term5 _111961 P.
Proof. exact (fun h0 : term6 _111961 P => @lem4872827 _111961 P h0). Qed.
Lemma lem4872843 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term156 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4872844 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) : (s = t) = (term156 _111988 s t).
Proof. exact (@lem4872843 _111988 s t). Qed.
Lemma lem4872845 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) : ((@INTER _111988 s t) = (term157 _111988 s t)) = (term158 _111988 s t).
Proof. exact (@lem4872844 _111988 (@INTER _111988 s t) (term157 _111988 s t)). Qed.
Lemma lem4872854 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) : (term158 _111988 s t) = ((@INTER _111988 s t) = (term157 _111988 s t)).
Proof. exact (SYM (@lem4872845 _111988 s t)). Qed.
Lemma lem4872862 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term159 A x s t) = (term160 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem4872863 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) (t : _111988 -> Prop) : (term159 _111988 x s t) = (term160 _111988 s x t).
Proof. exact (@lem4872862 _111988 s x t). Qed.
Lemma lem4872867 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4872868 {_111988 : Type'} (P : _111988 -> Prop) (x : _111988) : (@IN _111988 x P) = (P x).
Proof. exact (@lem4872867 _111988 P x). Qed.
Lemma lem4872869 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) : (@IN _111988 x s) = (s x).
Proof. exact (@lem4872868 _111988 s x). Qed.
Lemma lem4872870 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4872871 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) : (term161 _111988 x s) = (term162 _111988 s x).
Proof. exact (MK_COMB (@lem4872870) (@lem4872869 _111988 s x)). Qed.
Lemma lem4872873 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4872874 {_111988 : Type'} (P : _111988 -> Prop) (x : _111988) : (@IN _111988 x P) = (P x).
Proof. exact (@lem4872873 _111988 P x). Qed.
Lemma lem4872875 {_111988 : Type'} (t : _111988 -> Prop) (x : _111988) : (@IN _111988 x t) = (t x).
Proof. exact (@lem4872874 _111988 t x). Qed.
Lemma lem4872876 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : (term160 _111988 s x t) = (term163 _111988 s t x).
Proof. exact (MK_COMB (@lem4872871 _111988 s x) (@lem4872875 _111988 t x)). Qed.
Lemma lem4872879 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : (term159 _111988 x s t) = (term163 _111988 s t x).
Proof. exact (TRANS (@lem4872863 _111988 s x t) (@lem4872876 _111988 s t x)). Qed.
Lemma lem4872880 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4872881 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : (term164 _111988 x s t) = (term165 _111988 s t x).
Proof. exact (MK_COMB (@lem4872880) (@lem4872879 _111988 s t x)). Qed.
Lemma lem4872883 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term166 A x s t) = (term167 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem4872884 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) (t : _111988 -> Prop) : (term166 _111988 x s t) = (term167 _111988 s x t).
Proof. exact (@lem4872883 _111988 s x t). Qed.
Lemma lem4872885 {_111988 : Type'} (x : _111988) (s : _111988 -> Prop) (t : _111988 -> Prop) : (term168 _111988 x s t) = (term169 _111988 x s t).
Proof. exact (@lem4872884 _111988 (@UNIV _111988) x (term170 _111988 s t)). Qed.
Lemma lem4872889 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem4872890 {_111988 : Type'} (x : _111988) : (@IN _111988 x (@UNIV _111988)) = True.
Proof. exact (@lem4872889 _111988 x). Qed.
Lemma lem4872891 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4872892 {_111988 : Type'} (x : _111988) : (term171 _111988 x) = (and True).
Proof. exact (MK_COMB (@lem4872891) (@lem4872890 _111988 x)). Qed.
Lemma lem4872894 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term172 A x s t) = (term173 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem4872895 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) (t : _111988 -> Prop) : (term172 _111988 x s t) = (term173 _111988 s x t).
Proof. exact (@lem4872894 _111988 s x t). Qed.
Lemma lem4872896 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) (t : _111988 -> Prop) : (term174 _111988 x s t) = (term175 _111988 s x t).
Proof. exact (@lem4872895 _111988 (@DIFF _111988 (@UNIV _111988) s) x (@DIFF _111988 (@UNIV _111988) t)). Qed.
Lemma lem4872900 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term166 A x s t) = (term167 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem4872901 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) (t : _111988 -> Prop) : (term166 _111988 x s t) = (term167 _111988 s x t).
Proof. exact (@lem4872900 _111988 s x t). Qed.
Lemma lem4872902 {_111988 : Type'} (x : _111988) (s : _111988 -> Prop) : (term176 _111988 x s) = (term177 _111988 x s).
Proof. exact (@lem4872901 _111988 (@UNIV _111988) x s). Qed.
Lemma lem4872906 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem4872907 {_111988 : Type'} (x : _111988) : (@IN _111988 x (@UNIV _111988)) = True.
Proof. exact (@lem4872906 _111988 x). Qed.
Lemma lem4872908 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4872909 {_111988 : Type'} (x : _111988) : (term171 _111988 x) = (and True).
Proof. exact (MK_COMB (@lem4872908) (@lem4872907 _111988 x)). Qed.
Lemma lem4872911 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4872912 {_111988 : Type'} (P : _111988 -> Prop) (x : _111988) : (@IN _111988 x P) = (P x).
Proof. exact (@lem4872911 _111988 P x). Qed.
Lemma lem4872913 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) : (@IN _111988 x s) = (s x).
Proof. exact (@lem4872912 _111988 s x). Qed.
Lemma lem4872914 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4872915 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) : (term178 _111988 x s) = (term179 _111988 s x).
Proof. exact (MK_COMB (@lem4872914) (@lem4872913 _111988 s x)). Qed.
Lemma lem4872916 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) : (term177 _111988 x s) = (term180 _111988 s x).
Proof. exact (MK_COMB (@lem4872909 _111988 x) (@lem4872915 _111988 s x)). Qed.
Lemma lem4872918 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4872919 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) : (term180 _111988 s x) = (term179 _111988 s x).
Proof. exact (@lem4872918 (term179 _111988 s x)). Qed.
Lemma lem4872920 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) : (term177 _111988 x s) = (term179 _111988 s x).
Proof. exact (TRANS (@lem4872916 _111988 s x) (@lem4872919 _111988 s x)). Qed.
Lemma lem4872921 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) : (term176 _111988 x s) = (term179 _111988 s x).
Proof. exact (TRANS (@lem4872902 _111988 x s) (@lem4872920 _111988 s x)). Qed.
Lemma lem4872922 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4872923 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) : (term181 _111988 x s) = (term182 _111988 s x).
Proof. exact (MK_COMB (@lem4872922) (@lem4872921 _111988 s x)). Qed.
Lemma lem4872925 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term166 A x s t) = (term167 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem4872926 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) (t : _111988 -> Prop) : (term166 _111988 x s t) = (term167 _111988 s x t).
Proof. exact (@lem4872925 _111988 s x t). Qed.
Lemma lem4872927 {_111988 : Type'} (x : _111988) (t : _111988 -> Prop) : (term176 _111988 x t) = (term177 _111988 x t).
Proof. exact (@lem4872926 _111988 (@UNIV _111988) x t). Qed.
Lemma lem4872931 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem4872932 {_111988 : Type'} (x : _111988) : (@IN _111988 x (@UNIV _111988)) = True.
Proof. exact (@lem4872931 _111988 x). Qed.
Lemma lem4872933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4872934 {_111988 : Type'} (x : _111988) : (term171 _111988 x) = (and True).
Proof. exact (MK_COMB (@lem4872933) (@lem4872932 _111988 x)). Qed.
Lemma lem4872936 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4872937 {_111988 : Type'} (P : _111988 -> Prop) (x : _111988) : (@IN _111988 x P) = (P x).
Proof. exact (@lem4872936 _111988 P x). Qed.
Lemma lem4872938 {_111988 : Type'} (t : _111988 -> Prop) (x : _111988) : (@IN _111988 x t) = (t x).
Proof. exact (@lem4872937 _111988 t x). Qed.
Lemma lem4872939 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4872940 {_111988 : Type'} (t : _111988 -> Prop) (x : _111988) : (term178 _111988 x t) = (term179 _111988 t x).
Proof. exact (MK_COMB (@lem4872939) (@lem4872938 _111988 t x)). Qed.
Lemma lem4872941 {_111988 : Type'} (t : _111988 -> Prop) (x : _111988) : (term177 _111988 x t) = (term180 _111988 t x).
Proof. exact (MK_COMB (@lem4872934 _111988 x) (@lem4872940 _111988 t x)). Qed.
Lemma lem4872943 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4872944 {_111988 : Type'} (t : _111988 -> Prop) (x : _111988) : (term180 _111988 t x) = (term179 _111988 t x).
Proof. exact (@lem4872943 (term179 _111988 t x)). Qed.
Lemma lem4872945 {_111988 : Type'} (t : _111988 -> Prop) (x : _111988) : (term177 _111988 x t) = (term179 _111988 t x).
Proof. exact (TRANS (@lem4872941 _111988 t x) (@lem4872944 _111988 t x)). Qed.
Lemma lem4872946 {_111988 : Type'} (t : _111988 -> Prop) (x : _111988) : (term176 _111988 x t) = (term179 _111988 t x).
Proof. exact (TRANS (@lem4872927 _111988 x t) (@lem4872945 _111988 t x)). Qed.
Lemma lem4872947 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : (term175 _111988 s x t) = (term183 _111988 s t x).
Proof. exact (MK_COMB (@lem4872923 _111988 s x) (@lem4872946 _111988 t x)). Qed.
Lemma lem4872950 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : (term174 _111988 x s t) = (term183 _111988 s t x).
Proof. exact (TRANS (@lem4872896 _111988 s x t) (@lem4872947 _111988 s t x)). Qed.
Lemma lem4872951 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4872952 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : (term184 _111988 x s t) = (term185 _111988 s t x).
Proof. exact (MK_COMB (@lem4872951) (@lem4872950 _111988 s t x)). Qed.
Lemma lem4872953 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : (term169 _111988 x s t) = (term186 _111988 s t x).
Proof. exact (MK_COMB (@lem4872892 _111988 x) (@lem4872952 _111988 s t x)). Qed.
Lemma lem4872955 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4872956 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : (term186 _111988 s t x) = (term185 _111988 s t x).
Proof. exact (@lem4872955 (term185 _111988 s t x)). Qed.
Lemma lem4872959 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : (term169 _111988 x s t) = (term185 _111988 s t x).
Proof. exact (TRANS (@lem4872953 _111988 s t x) (@lem4872956 _111988 s t x)). Qed.
Lemma lem4872960 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : (term168 _111988 x s t) = (term185 _111988 s t x).
Proof. exact (TRANS (@lem4872885 _111988 x s t) (@lem4872959 _111988 s t x)). Qed.
Lemma lem4872961 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : ((term159 _111988 x s t) = (term168 _111988 x s t)) = ((term163 _111988 s t x) = (term185 _111988 s t x)).
Proof. exact (MK_COMB (@lem4872881 _111988 s t x) (@lem4872960 _111988 s t x)). Qed.
Lemma lem4872964 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) : (term187 _111988 s t) = (term188 _111988 s t).
Proof. exact (fun_ext (fun x : _111988 => @lem4872961 _111988 s t x)). Qed.
Lemma lem4872965 {_111988 : Type'} : (@all _111988) = (@all _111988).
Proof. exact (eq_refl (@all _111988)). Qed.
Lemma lem4872966 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) : (term158 _111988 s t) = (term189 _111988 s t).
Proof. exact (MK_COMB (@lem4872965 _111988) (@lem4872964 _111988 s t)). Qed.
Lemma lem4872971 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) : (term189 _111988 s t) = (term158 _111988 s t).
Proof. exact (SYM (@lem4872966 _111988 s t)). Qed.
Lemma lem4872973 (p : Prop) : p = (term2 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4872974 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) : (term189 _111988 s t) = (term190 _111988 s t).
Proof. exact (@lem4872973 (term189 _111988 s t)). Qed.
Lemma lem4872975 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) : (term190 _111988 s t) = (term189 _111988 s t).
Proof. exact (SYM (@lem4872974 _111988 s t)). Qed.
Lemma lem4872976 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (h1 : term191 _111988 s t) : term191 _111988 s t.
Proof. exact (h1). Qed.
Lemma lem4872979 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (h1 : term190 _111988 s t) : term190 _111988 s t.
Proof. exact (h1). Qed.
Lemma lem4872980 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) : term192 _111988 s t.
Proof. exact (fun h0 : term190 _111988 s t => @lem4872979 _111988 s t h0). Qed.
Lemma lem4872981 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (h1 : term192 _111988 s t) : term192 _111988 s t.
Proof. exact (h1). Qed.
Lemma lem4872982 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (h1 : term190 _111988 s t) : term190 _111988 s t.
Proof. exact (h1). Qed.
Lemma lem4872983 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (h1 : term190 _111988 s t) (h2 : term192 _111988 s t) : term190 _111988 s t.
Proof. exact (@lem4872981 _111988 s t h2 (@lem4872982 _111988 s t h1)). Qed.
Lemma lem4872984 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (h1 : term190 _111988 s t) : term193 _111988 s t.
Proof. exact (fun h0 : term192 _111988 s t => @lem4872983 _111988 s t h1 h0). Qed.
Lemma lem4872985 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (h1 : term192 _111988 s t) : term192 _111988 s t.
Proof. exact (h1). Qed.
Lemma lem4872986 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (h1 : term190 _111988 s t) (h2 : term192 _111988 s t) : term190 _111988 s t.
Proof. exact (@lem4872984 _111988 s t h1 (@lem4872985 _111988 s t h2)). Qed.
Lemma lem4872987 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (h1 : term192 _111988 s t) : term192 _111988 s t.
Proof. exact (fun h0 : term190 _111988 s t => @lem4872986 _111988 s t h0 h1). Qed.
Lemma lem4872988 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) : term194 _111988 s t.
Proof. exact (fun h0 : term192 _111988 s t => @lem4872987 _111988 s t h0). Qed.
Lemma lem4872991 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) : term192 _111988 s t.
Proof. exact (@lem4872988 _111988 s t (@lem4872980 _111988 s t)). Qed.
Lemma lem4872992 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) : term192 _111988 s t.
Proof. exact (@lem4872991 _111988 s t). Qed.
Lemma lem4873002 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4873003 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) : (term190 _111988 s t) = (term195 _111988 s t).
Proof. exact (@lem4873002 (term191 _111988 s t)). Qed.
Lemma lem4873005 (t : Prop) : (term139 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4873006 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) : (term195 _111988 s t) = (term189 _111988 s t).
Proof. exact (@lem4873005 (term189 _111988 s t)). Qed.
Lemma lem4873011 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) : (term190 _111988 s t) = (term189 _111988 s t).
Proof. exact (TRANS (@lem4873003 _111988 s t) (@lem4873006 _111988 s t)). Qed.
Lemma lem4873016 {_111988 : Type'} (t : _111988 -> Prop) : (term196 _111988 t) = (term197 _111988 t).
Proof. exact (fun_ext (fun s : _111988 -> Prop => @lem4873011 _111988 s t)). Qed.
Lemma lem4873017 {_111988 : Type'} : (@all (_111988 -> Prop)) = (@all (_111988 -> Prop)).
Proof. exact (eq_refl (@all (_111988 -> Prop))). Qed.
Lemma lem4873018 {_111988 : Type'} (t : _111988 -> Prop) : (term198 _111988 t) = (term199 _111988 t).
Proof. exact (MK_COMB (@lem4873017 _111988) (@lem4873016 _111988 t)). Qed.
Lemma lem4873023 {_111988 : Type'} : (term200 _111988) = (term201 _111988).
Proof. exact (fun_ext (fun t : _111988 -> Prop => @lem4873018 _111988 t)). Qed.
Lemma lem4873024 {_111988 : Type'} : (@all (_111988 -> Prop)) = (@all (_111988 -> Prop)).
Proof. exact (eq_refl (@all (_111988 -> Prop))). Qed.
Lemma lem4873033 {_111988 : Type'} : (term202 _111988) = (term203 _111988).
Proof. exact (MK_COMB (@lem4873024 _111988) (@lem4873023 _111988)). Qed.
Lemma lem4873052 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : ((term163 _111988 s t x) = (term185 _111988 s t x)) = ((term163 _111988 s t x) = (term185 _111988 s t x)).
Proof. exact (eq_refl ((term163 _111988 s t x) = (term185 _111988 s t x))). Qed.
Lemma lem4873053 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) : (term188 _111988 s t) = (term188 _111988 s t).
Proof. exact (fun_ext (fun x : _111988 => @lem4873052 _111988 s t x)). Qed.
Lemma lem4873054 {_111988 : Type'} : (@all _111988) = (@all _111988).
Proof. exact (eq_refl (@all _111988)). Qed.
Lemma lem4873055 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) : (term189 _111988 s t) = (term189 _111988 s t).
Proof. exact (MK_COMB (@lem4873054 _111988) (@lem4873053 _111988 s t)). Qed.
Lemma lem4873056 {_111988 : Type'} (t : _111988 -> Prop) : (term197 _111988 t) = (term197 _111988 t).
Proof. exact (fun_ext (fun s : _111988 -> Prop => @lem4873055 _111988 s t)). Qed.
Lemma lem4873057 {_111988 : Type'} : (@all (_111988 -> Prop)) = (@all (_111988 -> Prop)).
Proof. exact (eq_refl (@all (_111988 -> Prop))). Qed.
Lemma lem4873058 {_111988 : Type'} (t : _111988 -> Prop) : (term199 _111988 t) = (term199 _111988 t).
Proof. exact (MK_COMB (@lem4873057 _111988) (@lem4873056 _111988 t)). Qed.
Lemma lem4873059 {_111988 : Type'} : (term201 _111988) = (term201 _111988).
Proof. exact (fun_ext (fun t : _111988 -> Prop => @lem4873058 _111988 t)). Qed.
Lemma lem4873060 {_111988 : Type'} : (@all (_111988 -> Prop)) = (@all (_111988 -> Prop)).
Proof. exact (eq_refl (@all (_111988 -> Prop))). Qed.
Lemma lem4873061 {_111988 : Type'} : (term203 _111988) = (term203 _111988).
Proof. exact (MK_COMB (@lem4873060 _111988) (@lem4873059 _111988)). Qed.
Lemma lem4873086 {_111988 : Type'} : (term202 _111988) = (term203 _111988).
Proof. exact (TRANS (@lem4873033 _111988) (@lem4873061 _111988)). Qed.
Lemma lem4873087 {_111988 : Type'} : (term203 _111988) = (term202 _111988).
Proof. exact (SYM (@lem4873086 _111988)). Qed.
Lemma lem4873089 (p : Prop) : p = (term2 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4873090 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : ((term163 _111988 s t x) = (term185 _111988 s t x)) = (term204 _111988 s t x).
Proof. exact (@lem4873089 ((term163 _111988 s t x) = (term185 _111988 s t x))). Qed.
Lemma lem4873091 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : (term204 _111988 s t x) = ((term163 _111988 s t x) = (term185 _111988 s t x)).
Proof. exact (SYM (@lem4873090 _111988 s t x)). Qed.
Lemma lem4873092 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term205 _111988 s t x) : term205 _111988 s t x.
Proof. exact (h1). Qed.
Lemma lem4873101 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : (term206 _111988 s t x) = (term183 _111988 s t x).
Proof. exact (@lem17045 (s x) (t x)). Qed.
Lemma lem4873108 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) : (term207 _111988 s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem4873112 {_111988 : Type'} (t : _111988 -> Prop) (x : _111988) : (term207 _111988 t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem4873113 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4873114 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) : (term208 _111988 s x) = (term162 _111988 s x).
Proof. exact (MK_COMB (@lem4873113) (@lem4873108 _111988 s x)). Qed.
Lemma lem4873115 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : (term209 _111988 s t x) = (term163 _111988 s t x).
Proof. exact (MK_COMB (@lem4873114 _111988 s x) (@lem4873112 _111988 t x)). Qed.
Lemma lem4873116 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : (term185 _111988 s t x) = (term209 _111988 s t x).
Proof. exact (@lem17160 (term179 _111988 s x) (term179 _111988 t x)). Qed.
Lemma lem4873117 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : (term185 _111988 s t x) = (term163 _111988 s t x).
Proof. exact (TRANS (@lem4873116 _111988 s t x) (@lem4873115 _111988 s t x)). Qed.
Lemma lem4873122 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : (term210 _111988 s t x) = (term183 _111988 s t x).
Proof. exact (@lem16933 (term183 _111988 s t x)). Qed.
Lemma lem4873123 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4873124 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : (term211 _111988 s t x) = (term212 _111988 s t x).
Proof. exact (MK_COMB (@lem4873123) (@lem4873101 _111988 s t x)). Qed.
Lemma lem4873125 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : (term213 _111988 s t x) = (term214 _111988 s t x).
Proof. exact (MK_COMB (@lem4873124 _111988 s t x) (@lem4873117 _111988 s t x)). Qed.
Lemma lem4873127 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : (term215 _111988 s t x) = (term215 _111988 s t x).
Proof. exact (eq_refl (term215 _111988 s t x)). Qed.
Lemma lem4873128 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : (term216 _111988 s t x) = (term217 _111988 s t x).
Proof. exact (MK_COMB (@lem4873127 _111988 s t x) (@lem4873122 _111988 s t x)). Qed.
Lemma lem4873129 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4873130 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : (term218 _111988 s t x) = (term219 _111988 s t x).
Proof. exact (MK_COMB (@lem4873129) (@lem4873128 _111988 s t x)). Qed.
Lemma lem4873131 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : (term220 _111988 s t x) = (term221 _111988 s t x).
Proof. exact (MK_COMB (@lem4873130 _111988 s t x) (@lem4873125 _111988 s t x)). Qed.
Lemma lem4873132 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : (term205 _111988 s t x) = (term220 _111988 s t x).
Proof. exact (@lem17646 (term163 _111988 s t x) (term185 _111988 s t x)). Qed.
Lemma lem4873137 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : (term205 _111988 s t x) = (term221 _111988 s t x).
Proof. exact (TRANS (@lem4873132 _111988 s t x) (@lem4873131 _111988 s t x)). Qed.
Lemma lem4873192 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term205 _111988 s t x) : term221 _111988 s t x.
Proof. exact (EQ_MP (@lem4873137 _111988 s t x) (@lem4873092 _111988 s t x h1)). Qed.
Lemma lem4873193 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term217 _111988 s t x) : term217 _111988 s t x.
Proof. exact (h1). Qed.
Lemma lem4873194 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term214 _111988 s t x) : term214 _111988 s t x.
Proof. exact (h1). Qed.
Lemma lem4873195 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term217 _111988 s t x) : term183 _111988 s t x.
Proof. exact (proj2 (@lem4873193 _111988 s t x h1)). Qed.
Lemma lem4873196 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term217 _111988 s t x) : term163 _111988 s t x.
Proof. exact (proj1 (@lem4873193 _111988 s t x h1)). Qed.
Lemma lem4873201 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term214 _111988 s t x) : term163 _111988 s t x.
Proof. exact (proj2 (@lem4873194 _111988 s t x h1)). Qed.
Lemma lem4873202 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term214 _111988 s t x) : term183 _111988 s t x.
Proof. exact (proj1 (@lem4873194 _111988 s t x h1)). Qed.
Lemma lem4873218 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 s x) : term179 _111988 s x.
Proof. exact (h1). Qed.
Lemma lem4873230 {_111988 : Type'} (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 t x) : term179 _111988 t x.
Proof. exact (h1). Qed.
Lemma lem4873242 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 s x) : term179 _111988 s x.
Proof. exact (h1). Qed.
Lemma lem4873254 {_111988 : Type'} (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 t x) : term179 _111988 t x.
Proof. exact (h1). Qed.
Lemma lem4873260 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 s x) : term179 _111988 s x.
Proof. exact (h1). Qed.
Lemma lem4873266 {_111988 : Type'} (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 t x) : term179 _111988 t x.
Proof. exact (h1). Qed.
Lemma lem4873272 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 s x) : term179 _111988 s x.
Proof. exact (h1). Qed.
Lemma lem4873278 {_111988 : Type'} (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 t x) : term179 _111988 t x.
Proof. exact (h1). Qed.
Lemma lem4873280 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term217 _111988 s t x) : s x.
Proof. exact (proj1 (@lem4873196 _111988 s t x h1)). Qed.
Lemma lem4873281 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term217 _111988 s t x) : term222 _111988 s x.
Proof. exact (fun h0 : term179 _111988 s x => @lem4873280 _111988 s t x h1). Qed.
Lemma lem4873283 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4873284 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) : (term222 _111988 s x) = (s x).
Proof. exact (@lem4873283 (s x)). Qed.
Lemma lem4873285 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term217 _111988 s t x) : s x.
Proof. exact (EQ_MP (@lem4873284 _111988 s x) (@lem4873281 _111988 s t x h1)). Qed.
Lemma lem4873288 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4873290 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) : (term179 _111988 s x) = (term223 _111988 s x).
Proof. exact (@lem4873288 (s x)). Qed.
Lemma lem4873293 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 s x) : term223 _111988 s x.
Proof. exact (EQ_MP (@lem4873290 _111988 s x) (@lem4873260 _111988 s x h1)). Qed.
Lemma lem4873296 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 s x) (h2 : term217 _111988 s t x) : False.
Proof. exact (@lem4873293 _111988 s x h1 (@lem4873285 _111988 s t x h2)). Qed.
Lemma lem4873297 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 s x) (h2 : term217 _111988 s t x) : term152.
Proof. exact (fun h0 : ~ False => @lem4873296 _111988 s t x h1 h2). Qed.
Lemma lem4873299 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4873300 : term152 = False.
Proof. exact (@lem4873299 False). Qed.
Lemma lem4873301 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 s x) (h2 : term217 _111988 s t x) : False.
Proof. exact (EQ_MP (@lem4873300) (@lem4873297 _111988 s t x h1 h2)). Qed.
Lemma lem4873303 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term217 _111988 s t x) : t x.
Proof. exact (proj2 (@lem4873196 _111988 s t x h1)). Qed.
Lemma lem4873304 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term217 _111988 s t x) : term222 _111988 t x.
Proof. exact (fun h0 : term179 _111988 t x => @lem4873303 _111988 s t x h1). Qed.
Lemma lem4873306 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4873307 {_111988 : Type'} (t : _111988 -> Prop) (x : _111988) : (term222 _111988 t x) = (t x).
Proof. exact (@lem4873306 (t x)). Qed.
Lemma lem4873308 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term217 _111988 s t x) : t x.
Proof. exact (EQ_MP (@lem4873307 _111988 t x) (@lem4873304 _111988 s t x h1)). Qed.
Lemma lem4873311 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4873313 {_111988 : Type'} (t : _111988 -> Prop) (x : _111988) : (term179 _111988 t x) = (term223 _111988 t x).
Proof. exact (@lem4873311 (t x)). Qed.
Lemma lem4873316 {_111988 : Type'} (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 t x) : term223 _111988 t x.
Proof. exact (EQ_MP (@lem4873313 _111988 t x) (@lem4873266 _111988 t x h1)). Qed.
Lemma lem4873319 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 t x) (h2 : term217 _111988 s t x) : False.
Proof. exact (@lem4873316 _111988 t x h1 (@lem4873308 _111988 s t x h2)). Qed.
Lemma lem4873320 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 t x) (h2 : term217 _111988 s t x) : term152.
Proof. exact (fun h0 : ~ False => @lem4873319 _111988 s t x h1 h2). Qed.
Lemma lem4873322 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4873323 : term152 = False.
Proof. exact (@lem4873322 False). Qed.
Lemma lem4873324 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 t x) (h2 : term217 _111988 s t x) : False.
Proof. exact (EQ_MP (@lem4873323) (@lem4873320 _111988 s t x h1 h2)). Qed.
Lemma lem4873326 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term214 _111988 s t x) : s x.
Proof. exact (proj1 (@lem4873201 _111988 s t x h1)). Qed.
Lemma lem4873327 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term214 _111988 s t x) : term222 _111988 s x.
Proof. exact (fun h0 : term179 _111988 s x => @lem4873326 _111988 s t x h1). Qed.
Lemma lem4873329 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4873330 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) : (term222 _111988 s x) = (s x).
Proof. exact (@lem4873329 (s x)). Qed.
Lemma lem4873331 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term214 _111988 s t x) : s x.
Proof. exact (EQ_MP (@lem4873330 _111988 s x) (@lem4873327 _111988 s t x h1)). Qed.
Lemma lem4873334 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4873336 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) : (term179 _111988 s x) = (term223 _111988 s x).
Proof. exact (@lem4873334 (s x)). Qed.
Lemma lem4873339 {_111988 : Type'} (s : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 s x) : term223 _111988 s x.
Proof. exact (EQ_MP (@lem4873336 _111988 s x) (@lem4873272 _111988 s x h1)). Qed.
Lemma lem4873342 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 s x) (h2 : term214 _111988 s t x) : False.
Proof. exact (@lem4873339 _111988 s x h1 (@lem4873331 _111988 s t x h2)). Qed.
Lemma lem4873343 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 s x) (h2 : term214 _111988 s t x) : term152.
Proof. exact (fun h0 : ~ False => @lem4873342 _111988 s t x h1 h2). Qed.
Lemma lem4873345 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4873346 : term152 = False.
Proof. exact (@lem4873345 False). Qed.
Lemma lem4873347 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 s x) (h2 : term214 _111988 s t x) : False.
Proof. exact (EQ_MP (@lem4873346) (@lem4873343 _111988 s t x h1 h2)). Qed.
Lemma lem4873349 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term214 _111988 s t x) : t x.
Proof. exact (proj2 (@lem4873201 _111988 s t x h1)). Qed.
Lemma lem4873350 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term214 _111988 s t x) : term222 _111988 t x.
Proof. exact (fun h0 : term179 _111988 t x => @lem4873349 _111988 s t x h1). Qed.
Lemma lem4873352 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4873353 {_111988 : Type'} (t : _111988 -> Prop) (x : _111988) : (term222 _111988 t x) = (t x).
Proof. exact (@lem4873352 (t x)). Qed.
Lemma lem4873354 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term214 _111988 s t x) : t x.
Proof. exact (EQ_MP (@lem4873353 _111988 t x) (@lem4873350 _111988 s t x h1)). Qed.
Lemma lem4873357 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4873359 {_111988 : Type'} (t : _111988 -> Prop) (x : _111988) : (term179 _111988 t x) = (term223 _111988 t x).
Proof. exact (@lem4873357 (t x)). Qed.
Lemma lem4873362 {_111988 : Type'} (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 t x) : term223 _111988 t x.
Proof. exact (EQ_MP (@lem4873359 _111988 t x) (@lem4873278 _111988 t x h1)). Qed.
Lemma lem4873365 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 t x) (h2 : term214 _111988 s t x) : False.
Proof. exact (@lem4873362 _111988 t x h1 (@lem4873354 _111988 s t x h2)). Qed.
Lemma lem4873366 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 t x) (h2 : term214 _111988 s t x) : term152.
Proof. exact (fun h0 : ~ False => @lem4873365 _111988 s t x h1 h2). Qed.
Lemma lem4873368 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4873369 : term152 = False.
Proof. exact (@lem4873368 False). Qed.
Lemma lem4873370 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 t x) (h2 : term214 _111988 s t x) : False.
Proof. exact (EQ_MP (@lem4873369) (@lem4873366 _111988 s t x h1 h2)). Qed.
Lemma lem4873371 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 t x) (h2 : term214 _111988 s t x) : (term179 _111988 t x) = False.
Proof. exact (prop_ext (fun h3 : term179 _111988 t x => @lem4873370 _111988 s t x h1 h2) (fun h3 : False => @lem4873278 _111988 t x h1)). Qed.
Lemma lem4873372 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 t x) (h2 : term214 _111988 s t x) : False.
Proof. exact (EQ_MP (@lem4873371 _111988 s t x h1 h2) (@lem4873278 _111988 t x h1)). Qed.
Lemma lem4873373 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 s x) (h2 : term214 _111988 s t x) : (term179 _111988 s x) = False.
Proof. exact (prop_ext (fun h3 : term179 _111988 s x => @lem4873347 _111988 s t x h1 h2) (fun h3 : False => @lem4873272 _111988 s x h1)). Qed.
Lemma lem4873374 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 s x) (h2 : term214 _111988 s t x) : False.
Proof. exact (EQ_MP (@lem4873373 _111988 s t x h1 h2) (@lem4873272 _111988 s x h1)). Qed.
Lemma lem4873375 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 t x) (h2 : term217 _111988 s t x) : (term179 _111988 t x) = False.
Proof. exact (prop_ext (fun h3 : term179 _111988 t x => @lem4873324 _111988 s t x h1 h2) (fun h3 : False => @lem4873266 _111988 t x h1)). Qed.
Lemma lem4873376 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 t x) (h2 : term217 _111988 s t x) : False.
Proof. exact (EQ_MP (@lem4873375 _111988 s t x h1 h2) (@lem4873266 _111988 t x h1)). Qed.
Lemma lem4873377 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 s x) (h2 : term217 _111988 s t x) : (term179 _111988 s x) = False.
Proof. exact (prop_ext (fun h3 : term179 _111988 s x => @lem4873301 _111988 s t x h1 h2) (fun h3 : False => @lem4873260 _111988 s x h1)). Qed.
Lemma lem4873378 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 s x) (h2 : term217 _111988 s t x) : False.
Proof. exact (EQ_MP (@lem4873377 _111988 s t x h1 h2) (@lem4873260 _111988 s x h1)). Qed.
Lemma lem4873379 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 t x) (h2 : term214 _111988 s t x) : (term179 _111988 t x) = False.
Proof. exact (prop_ext (fun h3 : term179 _111988 t x => @lem4873372 _111988 s t x h1 h2) (fun h3 : False => @lem4873254 _111988 t x h1)). Qed.
Lemma lem4873380 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 t x) (h2 : term214 _111988 s t x) : False.
Proof. exact (EQ_MP (@lem4873379 _111988 s t x h1 h2) (@lem4873254 _111988 t x h1)). Qed.
Lemma lem4873381 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 s x) (h2 : term214 _111988 s t x) : (term179 _111988 s x) = False.
Proof. exact (prop_ext (fun h3 : term179 _111988 s x => @lem4873374 _111988 s t x h1 h2) (fun h3 : False => @lem4873242 _111988 s x h1)). Qed.
Lemma lem4873382 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 s x) (h2 : term214 _111988 s t x) : False.
Proof. exact (EQ_MP (@lem4873381 _111988 s t x h1 h2) (@lem4873242 _111988 s x h1)). Qed.
Lemma lem4873383 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 t x) (h2 : term217 _111988 s t x) : (term179 _111988 t x) = False.
Proof. exact (prop_ext (fun h3 : term179 _111988 t x => @lem4873376 _111988 s t x h1 h2) (fun h3 : False => @lem4873230 _111988 t x h1)). Qed.
Lemma lem4873384 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 t x) (h2 : term217 _111988 s t x) : False.
Proof. exact (EQ_MP (@lem4873383 _111988 s t x h1 h2) (@lem4873230 _111988 t x h1)). Qed.
Lemma lem4873385 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 s x) (h2 : term217 _111988 s t x) : (term179 _111988 s x) = False.
Proof. exact (prop_ext (fun h3 : term179 _111988 s x => @lem4873378 _111988 s t x h1 h2) (fun h3 : False => @lem4873218 _111988 s x h1)). Qed.
Lemma lem4873386 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 s x) (h2 : term217 _111988 s t x) : False.
Proof. exact (EQ_MP (@lem4873385 _111988 s t x h1 h2) (@lem4873218 _111988 s x h1)). Qed.
Lemma lem4873387 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 t x) (h2 : term214 _111988 s t x) : (term179 _111988 t x) = False.
Proof. exact (prop_ext (fun h3 : term179 _111988 t x => @lem4873380 _111988 s t x h1 h2) (fun h3 : False => @lem4873254 _111988 t x h1)). Qed.
Lemma lem4873388 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 t x) (h2 : term214 _111988 s t x) : False.
Proof. exact (EQ_MP (@lem4873387 _111988 s t x h1 h2) (@lem4873254 _111988 t x h1)). Qed.
Lemma lem4873389 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 s x) (h2 : term214 _111988 s t x) : (term179 _111988 s x) = False.
Proof. exact (prop_ext (fun h3 : term179 _111988 s x => @lem4873382 _111988 s t x h1 h2) (fun h3 : False => @lem4873242 _111988 s x h1)). Qed.
Lemma lem4873390 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 s x) (h2 : term214 _111988 s t x) : False.
Proof. exact (EQ_MP (@lem4873389 _111988 s t x h1 h2) (@lem4873242 _111988 s x h1)). Qed.
Lemma lem4873391 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 t x) (h2 : term217 _111988 s t x) : (term179 _111988 t x) = False.
Proof. exact (prop_ext (fun h3 : term179 _111988 t x => @lem4873384 _111988 s t x h1 h2) (fun h3 : False => @lem4873230 _111988 t x h1)). Qed.
Lemma lem4873392 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 t x) (h2 : term217 _111988 s t x) : False.
Proof. exact (EQ_MP (@lem4873391 _111988 s t x h1 h2) (@lem4873230 _111988 t x h1)). Qed.
Lemma lem4873393 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 s x) (h2 : term217 _111988 s t x) : (term179 _111988 s x) = False.
Proof. exact (prop_ext (fun h3 : term179 _111988 s x => @lem4873386 _111988 s t x h1 h2) (fun h3 : False => @lem4873218 _111988 s x h1)). Qed.
Lemma lem4873394 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term179 _111988 s x) (h2 : term217 _111988 s t x) : False.
Proof. exact (EQ_MP (@lem4873393 _111988 s t x h1 h2) (@lem4873218 _111988 s x h1)). Qed.
Lemma lem4873395 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term214 _111988 s t x) : False.
Proof. exact (or_elim (@lem4873202 _111988 s t x h1) (fun h0 : term179 _111988 s x => @lem4873390 _111988 s t x h0 h1) (fun h0 : term179 _111988 t x => @lem4873388 _111988 s t x h0 h1)). Qed.
Lemma lem4873396 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term217 _111988 s t x) : False.
Proof. exact (or_elim (@lem4873195 _111988 s t x h1) (fun h0 : term179 _111988 s x => @lem4873394 _111988 s t x h0 h1) (fun h0 : term179 _111988 t x => @lem4873392 _111988 s t x h0 h1)). Qed.
Lemma lem4873397 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term205 _111988 s t x) : False.
Proof. exact (or_elim (@lem4873192 _111988 s t x h1) (fun h0 : term217 _111988 s t x => @lem4873396 _111988 s t x h0) (fun h0 : term214 _111988 s t x => @lem4873395 _111988 s t x h0)). Qed.
Lemma lem4873398 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term205 _111988 s t x) : (term205 _111988 s t x) = False.
Proof. exact (prop_ext (fun h2 : term205 _111988 s t x => @lem4873397 _111988 s t x h1) (fun h2 : False => @lem4873092 _111988 s t x h1)). Qed.
Lemma lem4873399 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) (h1 : term205 _111988 s t x) : False.
Proof. exact (EQ_MP (@lem4873398 _111988 s t x h1) (@lem4873092 _111988 s t x h1)). Qed.
Lemma lem4873400 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : term204 _111988 s t x.
Proof. exact (fun h0 : term205 _111988 s t x => @lem4873399 _111988 s t x h0). Qed.
Lemma lem4873401 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (x : _111988) : (term163 _111988 s t x) = (term185 _111988 s t x).
Proof. exact (EQ_MP (@lem4873091 _111988 s t x) (@lem4873400 _111988 s t x)). Qed.
Lemma lem4873406 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) : term189 _111988 s t.
Proof. exact (fun x : _111988 => @lem4873401 _111988 s t x). Qed.
Lemma lem4873411 {_111988 : Type'} (t : _111988 -> Prop) : term199 _111988 t.
Proof. exact (fun s : _111988 -> Prop => @lem4873406 _111988 s t). Qed.
Lemma lem4873416 {_111988 : Type'} : term203 _111988.
Proof. exact (fun t : _111988 -> Prop => @lem4873411 _111988 t). Qed.
Lemma lem4873417 {_111988 : Type'} : term202 _111988.
Proof. exact (EQ_MP (@lem4873087 _111988) (@lem4873416 _111988)). Qed.
Lemma lem4873418 {_111988 : Type'} (t : _111988 -> Prop) : term224 _111988 t.
Proof. exact (@lem4873417 _111988 t). Qed.
Lemma lem4873419 {_111988 : Type'} (t : _111988 -> Prop) : (term224 _111988 t) = (term198 _111988 t).
Proof. exact (eq_refl (term224 _111988 t)). Qed.
Lemma lem4873420 {_111988 : Type'} (t : _111988 -> Prop) : term198 _111988 t.
Proof. exact (EQ_MP (@lem4873419 _111988 t) (@lem4873418 _111988 t)). Qed.
Lemma lem4873421 {_111988 : Type'} (t : _111988 -> Prop) (s : _111988 -> Prop) : term225 _111988 t s.
Proof. exact (@lem4873420 _111988 t s). Qed.
Lemma lem4873422 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) : (term225 _111988 t s) = (term190 _111988 s t).
Proof. exact (eq_refl (term225 _111988 t s)). Qed.
Lemma lem4873423 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) : term190 _111988 s t.
Proof. exact (EQ_MP (@lem4873422 _111988 s t) (@lem4873421 _111988 t s)). Qed.
Lemma lem4873425 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) : term190 _111988 s t.
Proof. exact (@lem4872992 _111988 s t (@lem4873423 _111988 s t)). Qed.
Lemma lem4873426 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (h1 : term191 _111988 s t) : False.
Proof. exact (@lem4873425 _111988 s t (@lem4872976 _111988 s t h1)). Qed.
Lemma lem4873427 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (h1 : term191 _111988 s t) : (term191 _111988 s t) = False.
Proof. exact (prop_ext (fun h2 : term191 _111988 s t => @lem4873426 _111988 s t h1) (fun h2 : False => @lem4872976 _111988 s t h1)). Qed.
Lemma lem4873428 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) (h1 : term191 _111988 s t) : False.
Proof. exact (EQ_MP (@lem4873427 _111988 s t h1) (@lem4872976 _111988 s t h1)). Qed.
Lemma lem4873429 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) : term190 _111988 s t.
Proof. exact (fun h0 : term191 _111988 s t => @lem4873428 _111988 s t h0). Qed.
Lemma lem4873430 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) : term189 _111988 s t.
Proof. exact (EQ_MP (@lem4872975 _111988 s t) (@lem4873429 _111988 s t)). Qed.
Lemma lem4873431 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) : term158 _111988 s t.
Proof. exact (EQ_MP (@lem4872971 _111988 s t) (@lem4873430 _111988 s t)). Qed.
Lemma lem4873433 {A : Type'} (P : type686 A) : term226 A P.
Proof. exact (@lem4871095 A P). Qed.
Lemma lem4873434 {A : Type'} (P : type686 A) : (term226 A P) = ((term227 A P) = (term228 A P)).
Proof. exact (eq_refl (term226 A P)). Qed.
Lemma lem4873447 (p : Prop) : p = (term2 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4873448 {_112000 : Type'} (P : type686 _112000) : ((term3 _112000 P) = (term4 _112000 P)) = (term5 _112000 P).
Proof. exact (@lem4873447 ((term3 _112000 P) = (term4 _112000 P))). Qed.
Lemma lem4873449 {_112000 : Type'} (P : type686 _112000) : (term5 _112000 P) = ((term3 _112000 P) = (term4 _112000 P)).
Proof. exact (SYM (@lem4873448 _112000 P)). Qed.
Lemma lem4873450 {_112000 : Type'} (P : type686 _112000) (h1 : term6 _112000 P) : term6 _112000 P.
Proof. exact (h1). Qed.
Lemma lem4873451 {_112000 : Type'} : term7 _112000.
Proof. exact (@lem3270825 _112000). Qed.
Lemma lem4873455 {_112000 : Type'} (P : type686 _112000) (h1 : term8 _112000 P) : term8 _112000 P.
Proof. exact (h1). Qed.
Lemma lem4873456 {_112000 : Type'} (P : type686 _112000) : term9 _112000 P.
Proof. exact (fun h0 : term8 _112000 P => @lem4873455 _112000 P h0). Qed.
Lemma lem4873457 {_112000 : Type'} (P : type686 _112000) (h1 : term9 _112000 P) : term9 _112000 P.
Proof. exact (h1). Qed.
Lemma lem4873458 {_112000 : Type'} (P : type686 _112000) (h1 : term8 _112000 P) : term8 _112000 P.
Proof. exact (h1). Qed.
Lemma lem4873459 {_112000 : Type'} (P : type686 _112000) (h1 : term8 _112000 P) (h2 : term9 _112000 P) : term8 _112000 P.
Proof. exact (@lem4873457 _112000 P h2 (@lem4873458 _112000 P h1)). Qed.
Lemma lem4873460 {_112000 : Type'} (P : type686 _112000) (h1 : term8 _112000 P) : term10 _112000 P.
Proof. exact (fun h0 : term9 _112000 P => @lem4873459 _112000 P h1 h0). Qed.
Lemma lem4873461 {_112000 : Type'} (P : type686 _112000) (h1 : term9 _112000 P) : term9 _112000 P.
Proof. exact (h1). Qed.
Lemma lem4873462 {_112000 : Type'} (P : type686 _112000) (h1 : term8 _112000 P) (h2 : term9 _112000 P) : term8 _112000 P.
Proof. exact (@lem4873460 _112000 P h1 (@lem4873461 _112000 P h2)). Qed.
Lemma lem4873463 {_112000 : Type'} (P : type686 _112000) (h1 : term9 _112000 P) : term9 _112000 P.
Proof. exact (fun h0 : term8 _112000 P => @lem4873462 _112000 P h0 h1). Qed.
Lemma lem4873464 {_112000 : Type'} (P : type686 _112000) : term11 _112000 P.
Proof. exact (fun h0 : term9 _112000 P => @lem4873463 _112000 P h0). Qed.
Lemma lem4873467 {_112000 : Type'} (P : type686 _112000) : term9 _112000 P.
Proof. exact (@lem4873464 _112000 P (@lem4873456 _112000 P)). Qed.
Lemma lem4873468 {_112000 : Type'} (P : type686 _112000) : term9 _112000 P.
Proof. exact (@lem4873467 _112000 P). Qed.
Lemma lem4873484 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4873485 {_112000 : Type'} : (term12 _112000) = (term13 _112000).
Proof. exact (@lem4873484 (term7 _112000)). Qed.
Lemma lem4873490 {_112000 : Type'} (P : type686 _112000) : (term14 _112000 P) = (term14 _112000 P).
Proof. exact (eq_refl (term14 _112000 P)). Qed.
Lemma lem4873491 {_112000 : Type'} (P : type686 _112000) : (term8 _112000 P) = (term15 _112000 P).
Proof. exact (MK_COMB (@lem4873490 _112000 P) (@lem4873485 _112000)). Qed.
Lemma lem4873494 {_112000 : Type'} : (term16 _112000) = (term17 _112000).
Proof. exact (fun_ext (fun P : type686 _112000 => @lem4873491 _112000 P)). Qed.
Lemma lem4873495 {_112000 : Type'} : (@all ((_112000 -> Prop) -> Prop)) = (@all ((_112000 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_112000 -> Prop) -> Prop))). Qed.
Lemma lem4873504 {_112000 : Type'} : (term18 _112000) = (term19 _112000).
Proof. exact (MK_COMB (@lem4873495 _112000) (@lem4873494 _112000)). Qed.
Lemma lem4873505 {_112000 : Type'} (s : _112000 -> Prop) : ((term1 _112000 s) = s) = ((term1 _112000 s) = s).
Proof. exact (eq_refl ((term1 _112000 s) = s)). Qed.
Lemma lem4873506 {_112000 : Type'} : (term20 _112000) = (term20 _112000).
Proof. exact (fun_ext (fun s : _112000 -> Prop => @lem4873505 _112000 s)). Qed.
Lemma lem4873507 {_112000 : Type'} : (@all (_112000 -> Prop)) = (@all (_112000 -> Prop)).
Proof. exact (eq_refl (@all (_112000 -> Prop))). Qed.
Lemma lem4873508 {_112000 : Type'} : (term7 _112000) = (term7 _112000).
Proof. exact (MK_COMB (@lem4873507 _112000) (@lem4873506 _112000)). Qed.
Lemma lem4873509 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4873510 {_112000 : Type'} : (term13 _112000) = (term13 _112000).
Proof. exact (MK_COMB (@lem4873509) (@lem4873508 _112000)). Qed.
Lemma lem4873511 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem4873512 {_112000 : Type'} (P : type686 _112000) : (term21 _112000 P) = (term21 _112000 P).
Proof. exact (fun_ext (fun s : _112000 -> Prop => @lem4873511 _112000 P s)). Qed.
Lemma lem4873513 {_112000 : Type'} : (@all (_112000 -> Prop)) = (@all (_112000 -> Prop)).
Proof. exact (eq_refl (@all (_112000 -> Prop))). Qed.
Lemma lem4873514 {_112000 : Type'} (P : type686 _112000) : (term4 _112000 P) = (term4 _112000 P).
Proof. exact (MK_COMB (@lem4873513 _112000) (@lem4873512 _112000 P)). Qed.
Lemma lem4873515 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (term22 _112000 P s) = (term22 _112000 P s).
Proof. exact (eq_refl (term22 _112000 P s)). Qed.
Lemma lem4873516 {_112000 : Type'} (P : type686 _112000) : (term23 _112000 P) = (term23 _112000 P).
Proof. exact (fun_ext (fun s : _112000 -> Prop => @lem4873515 _112000 P s)). Qed.
Lemma lem4873517 {_112000 : Type'} : (@all (_112000 -> Prop)) = (@all (_112000 -> Prop)).
Proof. exact (eq_refl (@all (_112000 -> Prop))). Qed.
Lemma lem4873518 {_112000 : Type'} (P : type686 _112000) : (term3 _112000 P) = (term3 _112000 P).
Proof. exact (MK_COMB (@lem4873517 _112000) (@lem4873516 _112000 P)). Qed.
Lemma lem4873519 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4873520 {_112000 : Type'} (P : type686 _112000) : (term24 _112000 P) = (term24 _112000 P).
Proof. exact (MK_COMB (@lem4873519) (@lem4873518 _112000 P)). Qed.
Lemma lem4873521 {_112000 : Type'} (P : type686 _112000) : ((term3 _112000 P) = (term4 _112000 P)) = ((term3 _112000 P) = (term4 _112000 P)).
Proof. exact (MK_COMB (@lem4873520 _112000 P) (@lem4873514 _112000 P)). Qed.
Lemma lem4873522 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4873523 {_112000 : Type'} (P : type686 _112000) : (term6 _112000 P) = (term6 _112000 P).
Proof. exact (MK_COMB (@lem4873522) (@lem4873521 _112000 P)). Qed.
Lemma lem4873524 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4873525 {_112000 : Type'} (P : type686 _112000) : (term14 _112000 P) = (term14 _112000 P).
Proof. exact (MK_COMB (@lem4873524) (@lem4873523 _112000 P)). Qed.
Lemma lem4873526 {_112000 : Type'} (P : type686 _112000) : (term15 _112000 P) = (term15 _112000 P).
Proof. exact (MK_COMB (@lem4873525 _112000 P) (@lem4873510 _112000)). Qed.
Lemma lem4873527 {_112000 : Type'} : (term17 _112000) = (term17 _112000).
Proof. exact (fun_ext (fun P : type686 _112000 => @lem4873526 _112000 P)). Qed.
Lemma lem4873528 {_112000 : Type'} : (@all ((_112000 -> Prop) -> Prop)) = (@all ((_112000 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_112000 -> Prop) -> Prop))). Qed.
Lemma lem4873529 {_112000 : Type'} : (term19 _112000) = (term19 _112000).
Proof. exact (MK_COMB (@lem4873528 _112000) (@lem4873527 _112000)). Qed.
Lemma lem4873558 {_112000 : Type'} : (term18 _112000) = (term19 _112000).
Proof. exact (TRANS (@lem4873504 _112000) (@lem4873529 _112000)). Qed.
Lemma lem4873559 {_112000 : Type'} : (term19 _112000) = (term18 _112000).
Proof. exact (SYM (@lem4873558 _112000)). Qed.
Lemma lem4873560 {_112000 : Type'} (P : type686 _112000) (h1 : term6 _112000 P) : term6 _112000 P.
Proof. exact (h1). Qed.
Lemma lem4873561 {_112000 : Type'} (h1 : term7 _112000) : term7 _112000.
Proof. exact (h1). Qed.
Lemma lem4873563 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (term22 _112000 P s) = (term22 _112000 P s).
Proof. exact (eq_refl (term22 _112000 P s)). Qed.
Lemma lem4873564 {_112000 : Type'} (P : type686 _112000) : (term25 _112000 P) = (term26 _112000 P).
Proof. exact (@lem18392 (_112000 -> Prop) P). Qed.
Lemma lem4873565 {_112000 : Type'} (P : type686 _112000) : (term27 _112000 P) = (term28 _112000 P).
Proof. exact (@lem4873564 _112000 (term23 _112000 P)). Qed.
Lemma lem4873566 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (term29 _112000 P s) = (term22 _112000 P s).
Proof. exact (eq_refl (term29 _112000 P s)). Qed.
Lemma lem4873567 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4873569 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (term30 _112000 P s) = (term31 _112000 P s).
Proof. exact (MK_COMB (@lem4873567) (@lem4873566 _112000 P s)). Qed.
Lemma lem4873570 {_112000 : Type'} (P : type686 _112000) : (term32 _112000 P) = (term33 _112000 P).
Proof. exact (fun_ext (fun s : _112000 -> Prop => @lem4873569 _112000 P s)). Qed.
Lemma lem4873571 {_112000 : Type'} : (@ex (_112000 -> Prop)) = (@ex (_112000 -> Prop)).
Proof. exact (eq_refl (@ex (_112000 -> Prop))). Qed.
Lemma lem4873572 {_112000 : Type'} (P : type686 _112000) : (term28 _112000 P) = (term34 _112000 P).
Proof. exact (MK_COMB (@lem4873571 _112000) (@lem4873570 _112000 P)). Qed.
Lemma lem4873573 {_112000 : Type'} (P : type686 _112000) : (term27 _112000 P) = (term34 _112000 P).
Proof. exact (TRANS (@lem4873565 _112000 P) (@lem4873572 _112000 P)). Qed.
Lemma lem4873574 {_112000 : Type'} (P : type686 _112000) : (term23 _112000 P) = (term23 _112000 P).
Proof. exact (fun_ext (fun s : _112000 -> Prop => @lem4873563 _112000 P s)). Qed.
Lemma lem4873575 {_112000 : Type'} : (@all (_112000 -> Prop)) = (@all (_112000 -> Prop)).
Proof. exact (eq_refl (@all (_112000 -> Prop))). Qed.
Lemma lem4873576 {_112000 : Type'} (P : type686 _112000) : (term3 _112000 P) = (term3 _112000 P).
Proof. exact (MK_COMB (@lem4873575 _112000) (@lem4873574 _112000 P)). Qed.
Lemma lem4873578 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem4873579 {_112000 : Type'} (P : type686 _112000) : (term25 _112000 P) = (term26 _112000 P).
Proof. exact (@lem18392 (_112000 -> Prop) P). Qed.
Lemma lem4873580 {_112000 : Type'} (P : type686 _112000) : (term35 _112000 P) = (term36 _112000 P).
Proof. exact (@lem4873579 _112000 (term21 _112000 P)). Qed.
Lemma lem4873581 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (term37 _112000 P s) = (P s).
Proof. exact (eq_refl (term37 _112000 P s)). Qed.
Lemma lem4873582 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4873584 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (term38 _112000 P s) = (term39 _112000 P s).
Proof. exact (MK_COMB (@lem4873582) (@lem4873581 _112000 P s)). Qed.
Lemma lem4873585 {_112000 : Type'} (P : type686 _112000) : (term40 _112000 P) = (term41 _112000 P).
Proof. exact (fun_ext (fun s : _112000 -> Prop => @lem4873584 _112000 P s)). Qed.
Lemma lem4873586 {_112000 : Type'} : (@ex (_112000 -> Prop)) = (@ex (_112000 -> Prop)).
Proof. exact (eq_refl (@ex (_112000 -> Prop))). Qed.
Lemma lem4873587 {_112000 : Type'} (P : type686 _112000) : (term36 _112000 P) = (term26 _112000 P).
Proof. exact (MK_COMB (@lem4873586 _112000) (@lem4873585 _112000 P)). Qed.
Lemma lem4873588 {_112000 : Type'} (P : type686 _112000) : (term35 _112000 P) = (term26 _112000 P).
Proof. exact (TRANS (@lem4873580 _112000 P) (@lem4873587 _112000 P)). Qed.
Lemma lem4873589 {_112000 : Type'} (P : type686 _112000) : (term21 _112000 P) = (term21 _112000 P).
Proof. exact (fun_ext (fun s : _112000 -> Prop => @lem4873578 _112000 P s)). Qed.
Lemma lem4873590 {_112000 : Type'} : (@all (_112000 -> Prop)) = (@all (_112000 -> Prop)).
Proof. exact (eq_refl (@all (_112000 -> Prop))). Qed.
Lemma lem4873591 {_112000 : Type'} (P : type686 _112000) : (term4 _112000 P) = (term4 _112000 P).
Proof. exact (MK_COMB (@lem4873590 _112000) (@lem4873589 _112000 P)). Qed.
Lemma lem4873592 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4873593 {_112000 : Type'} (P : type686 _112000) : (term42 _112000 P) = (term43 _112000 P).
Proof. exact (MK_COMB (@lem4873592) (@lem4873573 _112000 P)). Qed.
Lemma lem4873594 {_112000 : Type'} (P : type686 _112000) : (term44 _112000 P) = (term45 _112000 P).
Proof. exact (MK_COMB (@lem4873593 _112000 P) (@lem4873591 _112000 P)). Qed.
Lemma lem4873595 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4873596 {_112000 : Type'} (P : type686 _112000) : (term46 _112000 P) = (term46 _112000 P).
Proof. exact (MK_COMB (@lem4873595) (@lem4873576 _112000 P)). Qed.
Lemma lem4873597 {_112000 : Type'} (P : type686 _112000) : (term47 _112000 P) = (term48 _112000 P).
Proof. exact (MK_COMB (@lem4873596 _112000 P) (@lem4873588 _112000 P)). Qed.
Lemma lem4873598 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4873599 {_112000 : Type'} (P : type686 _112000) : (term49 _112000 P) = (term50 _112000 P).
Proof. exact (MK_COMB (@lem4873598) (@lem4873597 _112000 P)). Qed.
Lemma lem4873600 {_112000 : Type'} (P : type686 _112000) : (term51 _112000 P) = (term52 _112000 P).
Proof. exact (MK_COMB (@lem4873599 _112000 P) (@lem4873594 _112000 P)). Qed.
Lemma lem4873601 {_112000 : Type'} (P : type686 _112000) : (term6 _112000 P) = (term51 _112000 P).
Proof. exact (@lem17646 (term3 _112000 P) (term4 _112000 P)). Qed.
Lemma lem4873602 {_112000 : Type'} (P : type686 _112000) : (term6 _112000 P) = (term52 _112000 P).
Proof. exact (TRANS (@lem4873601 _112000 P) (@lem4873600 _112000 P)). Qed.
Lemma lem4873621 {A : Type'} (P : Prop) (Q : A -> Prop) : (term53 A P Q) = (term54 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4873622 {_112000 : Type'} (P : Prop) (Q : type686 _112000) : (term55 _112000 P Q) = (term56 _112000 P Q).
Proof. exact (@lem4873621 (_112000 -> Prop) P Q). Qed.
Lemma lem4873623 {_112000 : Type'} (P : type686 _112000) : (term57 _112000 P) = (term58 _112000 P).
Proof. exact (@lem4873622 _112000 (term3 _112000 P) (term41 _112000 P)). Qed.
Lemma lem4873624 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (term59 _112000 P s) = (term39 _112000 P s).
Proof. exact (eq_refl (term59 _112000 P s)). Qed.
Lemma lem4873625 {_112000 : Type'} (P : type686 _112000) : (term60 _112000 P) = (term41 _112000 P).
Proof. exact (fun_ext (fun s : _112000 -> Prop => @lem4873624 _112000 P s)). Qed.
Lemma lem4873626 {_112000 : Type'} : (@ex (_112000 -> Prop)) = (@ex (_112000 -> Prop)).
Proof. exact (eq_refl (@ex (_112000 -> Prop))). Qed.
Lemma lem4873627 {_112000 : Type'} (P : type686 _112000) : (term61 _112000 P) = (term26 _112000 P).
Proof. exact (MK_COMB (@lem4873626 _112000) (@lem4873625 _112000 P)). Qed.
Lemma lem4873628 {_112000 : Type'} (P : type686 _112000) : (term46 _112000 P) = (term46 _112000 P).
Proof. exact (eq_refl (term46 _112000 P)). Qed.
Lemma lem4873629 {_112000 : Type'} (P : type686 _112000) : (term57 _112000 P) = (term48 _112000 P).
Proof. exact (MK_COMB (@lem4873628 _112000 P) (@lem4873627 _112000 P)). Qed.
Lemma lem4873630 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4873631 {_112000 : Type'} (P : type686 _112000) : (term62 _112000 P) = (term63 _112000 P).
Proof. exact (MK_COMB (@lem4873630) (@lem4873629 _112000 P)). Qed.
Lemma lem4873632 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (term59 _112000 P s) = (term39 _112000 P s).
Proof. exact (eq_refl (term59 _112000 P s)). Qed.
Lemma lem4873633 {_112000 : Type'} (P : type686 _112000) : (term46 _112000 P) = (term46 _112000 P).
Proof. exact (eq_refl (term46 _112000 P)). Qed.
Lemma lem4873634 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (term64 _112000 P s) = (term65 _112000 P s).
Proof. exact (MK_COMB (@lem4873633 _112000 P) (@lem4873632 _112000 P s)). Qed.
Lemma lem4873635 {_112000 : Type'} (P : type686 _112000) : (term66 _112000 P) = (term67 _112000 P).
Proof. exact (fun_ext (fun s : _112000 -> Prop => @lem4873634 _112000 P s)). Qed.
Lemma lem4873636 {_112000 : Type'} : (@ex (_112000 -> Prop)) = (@ex (_112000 -> Prop)).
Proof. exact (eq_refl (@ex (_112000 -> Prop))). Qed.
Lemma lem4873637 {_112000 : Type'} (P : type686 _112000) : (term58 _112000 P) = (term68 _112000 P).
Proof. exact (MK_COMB (@lem4873636 _112000) (@lem4873635 _112000 P)). Qed.
Lemma lem4873638 {_112000 : Type'} (P : type686 _112000) : ((term57 _112000 P) = (term58 _112000 P)) = ((term48 _112000 P) = (term68 _112000 P)).
Proof. exact (MK_COMB (@lem4873631 _112000 P) (@lem4873637 _112000 P)). Qed.
Lemma lem4873639 {_112000 : Type'} (P : type686 _112000) : (term48 _112000 P) = (term68 _112000 P).
Proof. exact (EQ_MP (@lem4873638 _112000 P) (@lem4873623 _112000 P)). Qed.
Lemma lem4873640 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4873641 {_112000 : Type'} (P : type686 _112000) : (term50 _112000 P) = (term69 _112000 P).
Proof. exact (MK_COMB (@lem4873640) (@lem4873639 _112000 P)). Qed.
Lemma lem4873643 {A : Type'} (P : A -> Prop) (Q : Prop) : (term70 A P Q) = (term71 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4873644 {_112000 : Type'} (P : type686 _112000) (Q : Prop) : (term72 _112000 P Q) = (term73 _112000 P Q).
Proof. exact (@lem4873643 (_112000 -> Prop) P Q). Qed.
Lemma lem4873645 {_112000 : Type'} (P : type686 _112000) : (term74 _112000 P) = (term75 _112000 P).
Proof. exact (@lem4873644 _112000 (term33 _112000 P) (term4 _112000 P)). Qed.
Lemma lem4873646 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (term76 _112000 P s) = (term31 _112000 P s).
Proof. exact (eq_refl (term76 _112000 P s)). Qed.
Lemma lem4873647 {_112000 : Type'} (P : type686 _112000) : (term77 _112000 P) = (term33 _112000 P).
Proof. exact (fun_ext (fun s : _112000 -> Prop => @lem4873646 _112000 P s)). Qed.
Lemma lem4873648 {_112000 : Type'} : (@ex (_112000 -> Prop)) = (@ex (_112000 -> Prop)).
Proof. exact (eq_refl (@ex (_112000 -> Prop))). Qed.
Lemma lem4873649 {_112000 : Type'} (P : type686 _112000) : (term78 _112000 P) = (term34 _112000 P).
Proof. exact (MK_COMB (@lem4873648 _112000) (@lem4873647 _112000 P)). Qed.
Lemma lem4873650 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4873651 {_112000 : Type'} (P : type686 _112000) : (term79 _112000 P) = (term43 _112000 P).
Proof. exact (MK_COMB (@lem4873650) (@lem4873649 _112000 P)). Qed.
Lemma lem4873652 {_112000 : Type'} (P : type686 _112000) : (term4 _112000 P) = (term4 _112000 P).
Proof. exact (eq_refl (term4 _112000 P)). Qed.
Lemma lem4873653 {_112000 : Type'} (P : type686 _112000) : (term74 _112000 P) = (term45 _112000 P).
Proof. exact (MK_COMB (@lem4873651 _112000 P) (@lem4873652 _112000 P)). Qed.
Lemma lem4873654 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4873655 {_112000 : Type'} (P : type686 _112000) : (term80 _112000 P) = (term81 _112000 P).
Proof. exact (MK_COMB (@lem4873654) (@lem4873653 _112000 P)). Qed.
Lemma lem4873656 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (term76 _112000 P s) = (term31 _112000 P s).
Proof. exact (eq_refl (term76 _112000 P s)). Qed.
Lemma lem4873657 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4873658 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (term82 _112000 P s) = (term83 _112000 P s).
Proof. exact (MK_COMB (@lem4873657) (@lem4873656 _112000 P s)). Qed.
Lemma lem4873659 {_112000 : Type'} (P : type686 _112000) : (term4 _112000 P) = (term4 _112000 P).
Proof. exact (eq_refl (term4 _112000 P)). Qed.
Lemma lem4873660 {_112000 : Type'} (s : _112000 -> Prop) (P : type686 _112000) : (term84 _112000 s P) = (term85 _112000 s P).
Proof. exact (MK_COMB (@lem4873658 _112000 P s) (@lem4873659 _112000 P)). Qed.
Lemma lem4873661 {_112000 : Type'} (P : type686 _112000) : (term86 _112000 P) = (term87 _112000 P).
Proof. exact (fun_ext (fun s : _112000 -> Prop => @lem4873660 _112000 s P)). Qed.
Lemma lem4873662 {_112000 : Type'} : (@ex (_112000 -> Prop)) = (@ex (_112000 -> Prop)).
Proof. exact (eq_refl (@ex (_112000 -> Prop))). Qed.
Lemma lem4873663 {_112000 : Type'} (P : type686 _112000) : (term75 _112000 P) = (term88 _112000 P).
Proof. exact (MK_COMB (@lem4873662 _112000) (@lem4873661 _112000 P)). Qed.
Lemma lem4873664 {_112000 : Type'} (P : type686 _112000) : ((term74 _112000 P) = (term75 _112000 P)) = ((term45 _112000 P) = (term88 _112000 P)).
Proof. exact (MK_COMB (@lem4873655 _112000 P) (@lem4873663 _112000 P)). Qed.
Lemma lem4873665 {_112000 : Type'} (P : type686 _112000) : (term45 _112000 P) = (term88 _112000 P).
Proof. exact (EQ_MP (@lem4873664 _112000 P) (@lem4873645 _112000 P)). Qed.
Lemma lem4873666 {_112000 : Type'} (P : type686 _112000) : (term52 _112000 P) = (term89 _112000 P).
Proof. exact (MK_COMB (@lem4873641 _112000 P) (@lem4873665 _112000 P)). Qed.
Lemma lem4873668 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4873669 {_112000 : Type'} (P : type686 _112000) (Q : type686 _112000) : (term92 _112000 P Q) = (term93 _112000 P Q).
Proof. exact (@lem4873668 (_112000 -> Prop) P Q). Qed.
Lemma lem4873670 {_112000 : Type'} (P : type686 _112000) : (term94 _112000 P) = (term95 _112000 P).
Proof. exact (@lem4873669 _112000 (term67 _112000 P) (term87 _112000 P)). Qed.
Lemma lem4873671 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (term96 _112000 P s) = (term65 _112000 P s).
Proof. exact (eq_refl (term96 _112000 P s)). Qed.
Lemma lem4873672 {_112000 : Type'} (P : type686 _112000) : (term97 _112000 P) = (term67 _112000 P).
Proof. exact (fun_ext (fun s : _112000 -> Prop => @lem4873671 _112000 P s)). Qed.
Lemma lem4873673 {_112000 : Type'} : (@ex (_112000 -> Prop)) = (@ex (_112000 -> Prop)).
Proof. exact (eq_refl (@ex (_112000 -> Prop))). Qed.
Lemma lem4873674 {_112000 : Type'} (P : type686 _112000) : (term98 _112000 P) = (term68 _112000 P).
Proof. exact (MK_COMB (@lem4873673 _112000) (@lem4873672 _112000 P)). Qed.
Lemma lem4873675 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4873676 {_112000 : Type'} (P : type686 _112000) : (term99 _112000 P) = (term69 _112000 P).
Proof. exact (MK_COMB (@lem4873675) (@lem4873674 _112000 P)). Qed.
Lemma lem4873677 {_112000 : Type'} (s : _112000 -> Prop) (P : type686 _112000) : (term100 _112000 P s) = (term85 _112000 s P).
Proof. exact (eq_refl (term100 _112000 P s)). Qed.
Lemma lem4873678 {_112000 : Type'} (P : type686 _112000) : (term101 _112000 P) = (term87 _112000 P).
Proof. exact (fun_ext (fun s : _112000 -> Prop => @lem4873677 _112000 s P)). Qed.
Lemma lem4873679 {_112000 : Type'} : (@ex (_112000 -> Prop)) = (@ex (_112000 -> Prop)).
Proof. exact (eq_refl (@ex (_112000 -> Prop))). Qed.
Lemma lem4873680 {_112000 : Type'} (P : type686 _112000) : (term102 _112000 P) = (term88 _112000 P).
Proof. exact (MK_COMB (@lem4873679 _112000) (@lem4873678 _112000 P)). Qed.
Lemma lem4873681 {_112000 : Type'} (P : type686 _112000) : (term94 _112000 P) = (term89 _112000 P).
Proof. exact (MK_COMB (@lem4873676 _112000 P) (@lem4873680 _112000 P)). Qed.
Lemma lem4873682 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4873683 {_112000 : Type'} (P : type686 _112000) : (term103 _112000 P) = (term104 _112000 P).
Proof. exact (MK_COMB (@lem4873682) (@lem4873681 _112000 P)). Qed.
Lemma lem4873684 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (term96 _112000 P s) = (term65 _112000 P s).
Proof. exact (eq_refl (term96 _112000 P s)). Qed.
Lemma lem4873685 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4873686 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (term105 _112000 P s) = (term106 _112000 P s).
Proof. exact (MK_COMB (@lem4873685) (@lem4873684 _112000 P s)). Qed.
Lemma lem4873687 {_112000 : Type'} (s : _112000 -> Prop) (P : type686 _112000) : (term100 _112000 P s) = (term85 _112000 s P).
Proof. exact (eq_refl (term100 _112000 P s)). Qed.
Lemma lem4873688 {_112000 : Type'} (s : _112000 -> Prop) (P : type686 _112000) : (term107 _112000 P s) = (term108 _112000 s P).
Proof. exact (MK_COMB (@lem4873686 _112000 P s) (@lem4873687 _112000 s P)). Qed.
Lemma lem4873689 {_112000 : Type'} (P : type686 _112000) : (term109 _112000 P) = (term110 _112000 P).
Proof. exact (fun_ext (fun s : _112000 -> Prop => @lem4873688 _112000 s P)). Qed.
Lemma lem4873690 {_112000 : Type'} : (@ex (_112000 -> Prop)) = (@ex (_112000 -> Prop)).
Proof. exact (eq_refl (@ex (_112000 -> Prop))). Qed.
Lemma lem4873691 {_112000 : Type'} (P : type686 _112000) : (term95 _112000 P) = (term111 _112000 P).
Proof. exact (MK_COMB (@lem4873690 _112000) (@lem4873689 _112000 P)). Qed.
Lemma lem4873692 {_112000 : Type'} (P : type686 _112000) : ((term94 _112000 P) = (term95 _112000 P)) = ((term89 _112000 P) = (term111 _112000 P)).
Proof. exact (MK_COMB (@lem4873683 _112000 P) (@lem4873691 _112000 P)). Qed.
Lemma lem4873693 {_112000 : Type'} (P : type686 _112000) : (term89 _112000 P) = (term111 _112000 P).
Proof. exact (EQ_MP (@lem4873692 _112000 P) (@lem4873670 _112000 P)). Qed.
Lemma lem4873695 {_112000 : Type'} (P : type686 _112000) : (term52 _112000 P) = (term111 _112000 P).
Proof. exact (TRANS (@lem4873666 _112000 P) (@lem4873693 _112000 P)). Qed.
Lemma lem4873696 {_112000 : Type'} (P : type686 _112000) : (term6 _112000 P) = (term111 _112000 P).
Proof. exact (TRANS (@lem4873602 _112000 P) (@lem4873695 _112000 P)). Qed.
Lemma lem4873697 {_112000 : Type'} (P : type686 _112000) (h1 : term6 _112000 P) : term111 _112000 P.
Proof. exact (EQ_MP (@lem4873696 _112000 P) (@lem4873560 _112000 P h1)). Qed.
Lemma lem4873698 {_112000 : Type'} (s : _112000 -> Prop) : ((term1 _112000 s) = s) = ((term1 _112000 s) = s).
Proof. exact (eq_refl ((term1 _112000 s) = s)). Qed.
Lemma lem4873699 {_112000 : Type'} : (term20 _112000) = (term20 _112000).
Proof. exact (fun_ext (fun s : _112000 -> Prop => @lem4873698 _112000 s)). Qed.
Lemma lem4873700 {_112000 : Type'} : (@all (_112000 -> Prop)) = (@all (_112000 -> Prop)).
Proof. exact (eq_refl (@all (_112000 -> Prop))). Qed.
Lemma lem4873709 {_112000 : Type'} : (term7 _112000) = (term7 _112000).
Proof. exact (MK_COMB (@lem4873700 _112000) (@lem4873699 _112000)). Qed.
Lemma lem4873710 {_112000 : Type'} (h1 : term7 _112000) : term7 _112000.
Proof. exact (EQ_MP (@lem4873709 _112000) (@lem4873561 _112000 h1)). Qed.
Lemma lem4873711 {_112000 : Type'} (s : _112000 -> Prop) (P : type686 _112000) (h1 : term108 _112000 s P) : term108 _112000 s P.
Proof. exact (h1). Qed.
Lemma lem4873724 {_112000 : Type'} (s : _112000 -> Prop) : ((term1 _112000 s) = s) = ((term1 _112000 s) = s).
Proof. exact (eq_refl ((term1 _112000 s) = s)). Qed.
Lemma lem4873725 {_112000 : Type'} : (term20 _112000) = (term20 _112000).
Proof. exact (fun_ext (fun s : _112000 -> Prop => @lem4873724 _112000 s)). Qed.
Lemma lem4873726 {_112000 : Type'} : (@all (_112000 -> Prop)) = (@all (_112000 -> Prop)).
Proof. exact (eq_refl (@all (_112000 -> Prop))). Qed.
Lemma lem4873727 {_112000 : Type'} : (term7 _112000) = (term7 _112000).
Proof. exact (MK_COMB (@lem4873726 _112000) (@lem4873725 _112000)). Qed.
Lemma lem4873728 {_112000 : Type'} (h1 : term7 _112000) : term7 _112000.
Proof. exact (EQ_MP (@lem4873727 _112000) (@lem4873710 _112000 h1)). Qed.
Lemma lem4873731 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem4873732 {_112000 : Type'} (P : type686 _112000) : (term21 _112000 P) = (term21 _112000 P).
Proof. exact (fun_ext (fun s : _112000 -> Prop => @lem4873731 _112000 P s)). Qed.
Lemma lem4873733 {_112000 : Type'} : (@all (_112000 -> Prop)) = (@all (_112000 -> Prop)).
Proof. exact (eq_refl (@all (_112000 -> Prop))). Qed.
Lemma lem4873734 {_112000 : Type'} (P : type686 _112000) : (term4 _112000 P) = (term4 _112000 P).
Proof. exact (MK_COMB (@lem4873733 _112000) (@lem4873732 _112000 P)). Qed.
Lemma lem4873745 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (term83 _112000 P s) = (term83 _112000 P s).
Proof. exact (eq_refl (term83 _112000 P s)). Qed.
Lemma lem4873746 {_112000 : Type'} (s : _112000 -> Prop) (P : type686 _112000) : (term85 _112000 s P) = (term85 _112000 s P).
Proof. exact (MK_COMB (@lem4873745 _112000 P s) (@lem4873734 _112000 P)). Qed.
Lemma lem4873751 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (term39 _112000 P s) = (term39 _112000 P s).
Proof. exact (eq_refl (term39 _112000 P s)). Qed.
Lemma lem4873758 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (term22 _112000 P s) = (term22 _112000 P s).
Proof. exact (eq_refl (term22 _112000 P s)). Qed.
Lemma lem4873759 {_112000 : Type'} (P : type686 _112000) : (term23 _112000 P) = (term23 _112000 P).
Proof. exact (fun_ext (fun s : _112000 -> Prop => @lem4873758 _112000 P s)). Qed.
Lemma lem4873760 {_112000 : Type'} : (@all (_112000 -> Prop)) = (@all (_112000 -> Prop)).
Proof. exact (eq_refl (@all (_112000 -> Prop))). Qed.
Lemma lem4873761 {_112000 : Type'} (P : type686 _112000) : (term3 _112000 P) = (term3 _112000 P).
Proof. exact (MK_COMB (@lem4873760 _112000) (@lem4873759 _112000 P)). Qed.
Lemma lem4873762 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4873763 {_112000 : Type'} (P : type686 _112000) : (term46 _112000 P) = (term46 _112000 P).
Proof. exact (MK_COMB (@lem4873762) (@lem4873761 _112000 P)). Qed.
Lemma lem4873764 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (term65 _112000 P s) = (term65 _112000 P s).
Proof. exact (MK_COMB (@lem4873763 _112000 P) (@lem4873751 _112000 P s)). Qed.
Lemma lem4873765 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4873766 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (term106 _112000 P s) = (term106 _112000 P s).
Proof. exact (MK_COMB (@lem4873765) (@lem4873764 _112000 P s)). Qed.
Lemma lem4873767 {_112000 : Type'} (s : _112000 -> Prop) (P : type686 _112000) : (term108 _112000 s P) = (term108 _112000 s P).
Proof. exact (MK_COMB (@lem4873766 _112000 P s) (@lem4873746 _112000 s P)). Qed.
Lemma lem4873768 {_112000 : Type'} (s : _112000 -> Prop) (P : type686 _112000) (h1 : term108 _112000 s P) : term108 _112000 s P.
Proof. exact (EQ_MP (@lem4873767 _112000 s P) (@lem4873711 _112000 s P h1)). Qed.
Lemma lem4873769 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) (h1 : term65 _112000 P s) : term65 _112000 P s.
Proof. exact (h1). Qed.
Lemma lem4873770 {_112000 : Type'} (s : _112000 -> Prop) (P : type686 _112000) (h1 : term85 _112000 s P) : term85 _112000 s P.
Proof. exact (h1). Qed.
Lemma lem4873772 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) (h1 : term65 _112000 P s) : term3 _112000 P.
Proof. exact (proj1 (@lem4873769 _112000 P s h1)). Qed.
Lemma lem4873773 {_112000 : Type'} (s : _112000 -> Prop) (P : type686 _112000) (h1 : term85 _112000 s P) : term4 _112000 P.
Proof. exact (proj2 (@lem4873770 _112000 s P h1)). Qed.
Lemma lem4873776 {_112000 : Type'} (s : _112000 -> Prop) : ((term1 _112000 s) = s) = ((term1 _112000 s) = s).
Proof. exact (eq_refl ((term1 _112000 s) = s)). Qed.
Lemma lem4873777 {_112000 : Type'} : (term20 _112000) = (term20 _112000).
Proof. exact (fun_ext (fun s : _112000 -> Prop => @lem4873776 _112000 s)). Qed.
Lemma lem4873778 {_112000 : Type'} : (@all (_112000 -> Prop)) = (@all (_112000 -> Prop)).
Proof. exact (eq_refl (@all (_112000 -> Prop))). Qed.
Lemma lem4873780 {_112000 : Type'} : (term7 _112000) = (term7 _112000).
Proof. exact (MK_COMB (@lem4873778 _112000) (@lem4873777 _112000)). Qed.
Lemma lem4873781 {_112000 : Type'} (h1 : term7 _112000) : term7 _112000.
Proof. exact (EQ_MP (@lem4873780 _112000) (@lem4873728 _112000 h1)). Qed.
Lemma lem4873783 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (term22 _112000 P s) = (term22 _112000 P s).
Proof. exact (eq_refl (term22 _112000 P s)). Qed.
Lemma lem4873784 {_112000 : Type'} (P : type686 _112000) : (term23 _112000 P) = (term23 _112000 P).
Proof. exact (fun_ext (fun s : _112000 -> Prop => @lem4873783 _112000 P s)). Qed.
Lemma lem4873785 {_112000 : Type'} : (@all (_112000 -> Prop)) = (@all (_112000 -> Prop)).
Proof. exact (eq_refl (@all (_112000 -> Prop))). Qed.
Lemma lem4873787 {_112000 : Type'} (P : type686 _112000) : (term3 _112000 P) = (term3 _112000 P).
Proof. exact (MK_COMB (@lem4873785 _112000) (@lem4873784 _112000 P)). Qed.
Lemma lem4873788 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) (h1 : term65 _112000 P s) : term3 _112000 P.
Proof. exact (EQ_MP (@lem4873787 _112000 P) (@lem4873772 _112000 P s h1)). Qed.
Lemma lem4873805 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem4873806 {_112000 : Type'} (P : type686 _112000) : (term21 _112000 P) = (term21 _112000 P).
Proof. exact (fun_ext (fun s : _112000 -> Prop => @lem4873805 _112000 P s)). Qed.
Lemma lem4873807 {_112000 : Type'} : (@all (_112000 -> Prop)) = (@all (_112000 -> Prop)).
Proof. exact (eq_refl (@all (_112000 -> Prop))). Qed.
Lemma lem4873809 {_112000 : Type'} (P : type686 _112000) : (term4 _112000 P) = (term4 _112000 P).
Proof. exact (MK_COMB (@lem4873807 _112000) (@lem4873806 _112000 P)). Qed.
Lemma lem4873810 {_112000 : Type'} (s : _112000 -> Prop) (P : type686 _112000) (h1 : term85 _112000 s P) : term4 _112000 P.
Proof. exact (EQ_MP (@lem4873809 _112000 P) (@lem4873773 _112000 s P h1)). Qed.
Lemma lem4873811 {_112000 : Type'} (_60285 : _112000 -> Prop) (h1 : term7 _112000) : term0 _112000 _60285.
Proof. exact (@lem4873781 _112000 h1 _60285). Qed.
Lemma lem4873812 {_112000 : Type'} (_60285 : _112000 -> Prop) : (term0 _112000 _60285) = ((term1 _112000 _60285) = _60285).
Proof. exact (eq_refl (term0 _112000 _60285)). Qed.
Lemma lem4873814 {_112000 : Type'} (_60286 : _112000 -> Prop) (P : type686 _112000) (s : _112000 -> Prop) (h1 : term65 _112000 P s) : term29 _112000 P _60286.
Proof. exact (@lem4873788 _112000 P s h1 _60286). Qed.
Lemma lem4873815 {_112000 : Type'} (P : type686 _112000) (_60286 : _112000 -> Prop) : (term29 _112000 P _60286) = (term22 _112000 P _60286).
Proof. exact (eq_refl (term29 _112000 P _60286)). Qed.
Lemma lem4873820 {_112000 : Type'} (_60288 : _112000 -> Prop) (s : _112000 -> Prop) (P : type686 _112000) (h1 : term85 _112000 s P) : term37 _112000 P _60288.
Proof. exact (@lem4873810 _112000 s P h1 _60288). Qed.
Lemma lem4873821 {_112000 : Type'} (P : type686 _112000) (_60288 : _112000 -> Prop) : (term37 _112000 P _60288) = (P _60288).
Proof. exact (eq_refl (term37 _112000 P _60288)). Qed.
Lemma lem4873828 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) (h1 : term65 _112000 P s) : term39 _112000 P s.
Proof. exact (proj2 (@lem4873769 _112000 P s h1)). Qed.
Lemma lem4873832 {_112000 : Type'} (s : _112000 -> Prop) (P : type686 _112000) (h1 : term85 _112000 s P) : term31 _112000 P s.
Proof. exact (proj1 (@lem4873770 _112000 s P h1)). Qed.
Lemma lem4873835 {_112000 : Type'} (P : type686 _112000) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4873836 {_112000 : Type'} (_60289 : _112000 -> Prop) (_60290 : _112000 -> Prop) (h1 : _60289 = _60290) : _60289 = _60290.
Proof. exact (h1). Qed.
Lemma lem4873837 {_112000 : Type'} (P : type686 _112000) (_60289 : _112000 -> Prop) (_60290 : _112000 -> Prop) (h1 : _60289 = _60290) : (P _60289) = (P _60290).
Proof. exact (MK_COMB (@lem4873835 _112000 P) (@lem4873836 _112000 _60289 _60290 h1)). Qed.
Lemma lem4873839 (b : Prop) (a : Prop) : term112 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem4873840 {_112000 : Type'} (_60290 : _112000 -> Prop) (P : type686 _112000) (_60289 : _112000 -> Prop) : term113 _112000 _60290 P _60289.
Proof. exact (@lem4873839 (P _60290) (P _60289)). Qed.
Lemma lem4873841 {_112000 : Type'} (P : type686 _112000) (_60289 : _112000 -> Prop) (_60290 : _112000 -> Prop) (h1 : _60289 = _60290) : term114 _112000 _60290 P _60289.
Proof. exact (@lem4873840 _112000 _60290 P _60289 (@lem4873837 _112000 P _60289 _60290 h1)). Qed.
Lemma lem4873842 {_112000 : Type'} (_60290 : _112000 -> Prop) (P : type686 _112000) (_60289 : _112000 -> Prop) : term115 _112000 _60290 P _60289.
Proof. exact (fun h0 : _60289 = _60290 => @lem4873841 _112000 P _60289 _60290 h0). Qed.
Lemma lem4873844 (a : Prop) (b : Prop) : (a -> b) = (term116 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4873845 {_112000 : Type'} (_60290 : _112000 -> Prop) (P : type686 _112000) (_60289 : _112000 -> Prop) : (term115 _112000 _60290 P _60289) = (term117 _112000 _60290 P _60289).
Proof. exact (@lem4873844 (_60289 = _60290) (term114 _112000 _60290 P _60289)). Qed.
Lemma lem4873846 {_112000 : Type'} (_60290 : _112000 -> Prop) (P : type686 _112000) (_60289 : _112000 -> Prop) : term117 _112000 _60290 P _60289.
Proof. exact (EQ_MP (@lem4873845 _112000 _60290 P _60289) (@lem4873842 _112000 _60290 P _60289)). Qed.
Lemma lem4873865 {_112000 : Type'} (_60285 : _112000 -> Prop) (h1 : term7 _112000) : (term1 _112000 _60285) = _60285.
Proof. exact (EQ_MP (@lem4873812 _112000 _60285) (@lem4873811 _112000 _60285 h1)). Qed.
Lemma lem4873866 {_112000 : Type'} (_60285 : _112000 -> Prop) (h1 : term7 _112000) : (term1 _112000 _60285) = _60285.
Proof. exact (@lem4873865 _112000 _60285 h1). Qed.
Lemma lem4873867 {_112000 : Type'} (s : _112000 -> Prop) (h1 : term7 _112000) : (term1 _112000 s) = s.
Proof. exact (@lem4873866 _112000 s h1). Qed.
Lemma lem4873868 {_112000 : Type'} (s : _112000 -> Prop) (h1 : term7 _112000) : term118 _112000 s.
Proof. exact (fun h0 : term119 _112000 s => @lem4873867 _112000 s h1). Qed.
Lemma lem4873870 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4873871 {_112000 : Type'} (s : _112000 -> Prop) : (term118 _112000 s) = ((term1 _112000 s) = s).
Proof. exact (@lem4873870 ((term1 _112000 s) = s)). Qed.
Lemma lem4873872 {_112000 : Type'} (s : _112000 -> Prop) (h1 : term7 _112000) : (term1 _112000 s) = s.
Proof. exact (EQ_MP (@lem4873871 _112000 s) (@lem4873868 _112000 s h1)). Qed.
Lemma lem4873874 {_112000 : Type'} (_60286 : _112000 -> Prop) (P : type686 _112000) (s : _112000 -> Prop) (h1 : term65 _112000 P s) : term22 _112000 P _60286.
Proof. exact (EQ_MP (@lem4873815 _112000 P _60286) (@lem4873814 _112000 _60286 P s h1)). Qed.
Lemma lem4873875 {_112000 : Type'} (_60286 : _112000 -> Prop) (P : type686 _112000) (s : _112000 -> Prop) (h1 : term65 _112000 P s) : term22 _112000 P _60286.
Proof. exact (@lem4873874 _112000 _60286 P s h1). Qed.
Lemma lem4873876 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) (h1 : term65 _112000 P s) : term121 _112000 P s.
Proof. exact (@lem4873875 _112000 (@DIFF _112000 (@UNIV _112000) s) P s h1). Qed.
Lemma lem4873877 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) (h1 : term65 _112000 P s) : term122 _112000 P s.
Proof. exact (fun h0 : term123 _112000 P s => @lem4873876 _112000 P s h1). Qed.
Lemma lem4873879 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4873880 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (term122 _112000 P s) = (term121 _112000 P s).
Proof. exact (@lem4873879 (term121 _112000 P s)). Qed.
Lemma lem4873881 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) (h1 : term65 _112000 P s) : term121 _112000 P s.
Proof. exact (EQ_MP (@lem4873880 _112000 P s) (@lem4873877 _112000 P s h1)). Qed.
Lemma lem4873887 (q : Prop) (p : Prop) (r : Prop) : (term124 p q r) = (term124 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4873888 {_112000 : Type'} (_60290 : _112000 -> Prop) (P : type686 _112000) (_60289 : _112000 -> Prop) : (term117 _112000 _60290 P _60289) = (term125 _112000 _60290 P _60289).
Proof. exact (@lem4873887 (P _60290) (term126 _112000 _60289 _60290) (term39 _112000 P _60289)). Qed.
Lemma lem4873902 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4873903 {_112000 : Type'} (P : type686 _112000) (_60289 : _112000 -> Prop) (_60290 : _112000 -> Prop) : (term127 _112000 _60290 P _60289) = (term128 _112000 P _60289 _60290).
Proof. exact (@lem4873902 (term39 _112000 P _60289) (term126 _112000 _60289 _60290)). Qed.
Lemma lem4873911 {_112000 : Type'} (P : type686 _112000) (_60290 : _112000 -> Prop) : (term129 _112000 P _60290) = (term129 _112000 P _60290).
Proof. exact (eq_refl (term129 _112000 P _60290)). Qed.
Lemma lem4873912 {_112000 : Type'} (P : type686 _112000) (_60289 : _112000 -> Prop) (_60290 : _112000 -> Prop) : (term125 _112000 _60290 P _60289) = (term130 _112000 P _60289 _60290).
Proof. exact (MK_COMB (@lem4873911 _112000 P _60290) (@lem4873903 _112000 P _60289 _60290)). Qed.
Lemma lem4873923 {_112000 : Type'} (P : type686 _112000) (_60289 : _112000 -> Prop) (_60290 : _112000 -> Prop) : (term117 _112000 _60290 P _60289) = (term130 _112000 P _60289 _60290).
Proof. exact (TRANS (@lem4873888 _112000 _60290 P _60289) (@lem4873912 _112000 P _60289 _60290)). Qed.
Lemma lem4873924 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4873925 {_112000 : Type'} (P : type686 _112000) (_60289 : _112000 -> Prop) (_60290 : _112000 -> Prop) : (term131 _112000 _60290 P _60289) = (term132 _112000 P _60289 _60290).
Proof. exact (MK_COMB (@lem4873924) (@lem4873923 _112000 P _60289 _60290)). Qed.
Lemma lem4873939 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4873940 {_112000 : Type'} (P : type686 _112000) (_60289 : _112000 -> Prop) (_60290 : _112000 -> Prop) : (term127 _112000 _60290 P _60289) = (term128 _112000 P _60289 _60290).
Proof. exact (@lem4873939 (term39 _112000 P _60289) (term126 _112000 _60289 _60290)). Qed.
Lemma lem4873948 {_112000 : Type'} (P : type686 _112000) (_60290 : _112000 -> Prop) : (term129 _112000 P _60290) = (term129 _112000 P _60290).
Proof. exact (eq_refl (term129 _112000 P _60290)). Qed.
Lemma lem4873949 {_112000 : Type'} (P : type686 _112000) (_60289 : _112000 -> Prop) (_60290 : _112000 -> Prop) : (term125 _112000 _60290 P _60289) = (term130 _112000 P _60289 _60290).
Proof. exact (MK_COMB (@lem4873948 _112000 P _60290) (@lem4873940 _112000 P _60289 _60290)). Qed.
Lemma lem4873960 {_112000 : Type'} (P : type686 _112000) (_60289 : _112000 -> Prop) (_60290 : _112000 -> Prop) : ((term117 _112000 _60290 P _60289) = (term125 _112000 _60290 P _60289)) = ((term130 _112000 P _60289 _60290) = (term130 _112000 P _60289 _60290)).
Proof. exact (MK_COMB (@lem4873925 _112000 P _60289 _60290) (@lem4873949 _112000 P _60289 _60290)). Qed.
Lemma lem4873962 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4873963 (x : Prop) : (x = x) = True.
Proof. exact (@lem4873962 Prop x). Qed.
Lemma lem4873964 {_112000 : Type'} (P : type686 _112000) (_60289 : _112000 -> Prop) (_60290 : _112000 -> Prop) : ((term130 _112000 P _60289 _60290) = (term130 _112000 P _60289 _60290)) = True.
Proof. exact (@lem4873963 (term130 _112000 P _60289 _60290)). Qed.
Lemma lem4873965 {_112000 : Type'} (_60290 : _112000 -> Prop) (P : type686 _112000) (_60289 : _112000 -> Prop) : ((term117 _112000 _60290 P _60289) = (term125 _112000 _60290 P _60289)) = True.
Proof. exact (TRANS (@lem4873960 _112000 P _60289 _60290) (@lem4873964 _112000 P _60289 _60290)). Qed.
Lemma lem4873966 {_112000 : Type'} (_60290 : _112000 -> Prop) (P : type686 _112000) (_60289 : _112000 -> Prop) : True = ((term117 _112000 _60290 P _60289) = (term125 _112000 _60290 P _60289)).
Proof. exact (SYM (@lem4873965 _112000 _60290 P _60289)). Qed.
Lemma lem4873967 {_112000 : Type'} (_60290 : _112000 -> Prop) (P : type686 _112000) (_60289 : _112000 -> Prop) : (term117 _112000 _60290 P _60289) = (term125 _112000 _60290 P _60289).
Proof. exact (EQ_MP (@lem4873966 _112000 _60290 P _60289) (@lem0)). Qed.
Lemma lem4873968 {_112000 : Type'} (_60290 : _112000 -> Prop) (P : type686 _112000) (_60289 : _112000 -> Prop) : term125 _112000 _60290 P _60289.
Proof. exact (EQ_MP (@lem4873967 _112000 _60290 P _60289) (@lem4873846 _112000 _60290 P _60289)). Qed.
Lemma lem4873970 (b : Prop) (a : Prop) : (a \/ b) = (term133 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4873971 {_112000 : Type'} (_60289 : _112000 -> Prop) (P : type686 _112000) (_60290 : _112000 -> Prop) : (term125 _112000 _60290 P _60289) = (term134 _112000 _60289 P _60290).
Proof. exact (@lem4873970 (term127 _112000 _60290 P _60289) (P _60290)). Qed.
Lemma lem4873973 (a : Prop) (b : Prop) : (term135 a b) = (term136 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4873974 {_112000 : Type'} (_60290 : _112000 -> Prop) (P : type686 _112000) (_60289 : _112000 -> Prop) : (term137 _112000 _60290 P _60289) = (term138 _112000 _60290 P _60289).
Proof. exact (@lem4873973 (term126 _112000 _60289 _60290) (term39 _112000 P _60289)). Qed.
Lemma lem4873976 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4873977 {_112000 : Type'} (_60289 : _112000 -> Prop) (_60290 : _112000 -> Prop) : (term140 _112000 _60289 _60290) = (_60289 = _60290).
Proof. exact (@lem4873976 (_60289 = _60290)). Qed.
Lemma lem4873978 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4873979 {_112000 : Type'} (_60289 : _112000 -> Prop) (_60290 : _112000 -> Prop) : (term141 _112000 _60289 _60290) = (term142 _112000 _60289 _60290).
Proof. exact (MK_COMB (@lem4873978) (@lem4873977 _112000 _60289 _60290)). Qed.
Lemma lem4873981 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4873982 {_112000 : Type'} (P : type686 _112000) (_60289 : _112000 -> Prop) : (term143 _112000 P _60289) = (P _60289).
Proof. exact (@lem4873981 (P _60289)). Qed.
Lemma lem4873983 {_112000 : Type'} (_60290 : _112000 -> Prop) (P : type686 _112000) (_60289 : _112000 -> Prop) : (term138 _112000 _60290 P _60289) = (term144 _112000 _60290 P _60289).
Proof. exact (MK_COMB (@lem4873979 _112000 _60289 _60290) (@lem4873982 _112000 P _60289)). Qed.
Lemma lem4873984 {_112000 : Type'} (_60290 : _112000 -> Prop) (P : type686 _112000) (_60289 : _112000 -> Prop) : (term137 _112000 _60290 P _60289) = (term144 _112000 _60290 P _60289).
Proof. exact (TRANS (@lem4873974 _112000 _60290 P _60289) (@lem4873983 _112000 _60290 P _60289)). Qed.
Lemma lem4873985 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4873986 {_112000 : Type'} (_60290 : _112000 -> Prop) (P : type686 _112000) (_60289 : _112000 -> Prop) : (term145 _112000 _60290 P _60289) = (term146 _112000 _60290 P _60289).
Proof. exact (MK_COMB (@lem4873985) (@lem4873984 _112000 _60290 P _60289)). Qed.
Lemma lem4873987 {_112000 : Type'} (P : type686 _112000) (_60290 : _112000 -> Prop) : (P _60290) = (P _60290).
Proof. exact (eq_refl (P _60290)). Qed.
Lemma lem4873988 {_112000 : Type'} (_60289 : _112000 -> Prop) (P : type686 _112000) (_60290 : _112000 -> Prop) : (term134 _112000 _60289 P _60290) = (term147 _112000 _60289 P _60290).
Proof. exact (MK_COMB (@lem4873986 _112000 _60290 P _60289) (@lem4873987 _112000 P _60290)). Qed.
Lemma lem4873989 {_112000 : Type'} (_60289 : _112000 -> Prop) (P : type686 _112000) (_60290 : _112000 -> Prop) : (term125 _112000 _60290 P _60289) = (term147 _112000 _60289 P _60290).
Proof. exact (TRANS (@lem4873971 _112000 _60289 P _60290) (@lem4873988 _112000 _60289 P _60290)). Qed.
Lemma lem4873991 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) (h1 : term7 _112000) (h2 : term65 _112000 P s) : term148 _112000 P s.
Proof. exact (conj (@lem4873872 _112000 s h1) (@lem4873881 _112000 P s h2)). Qed.
Lemma lem4873993 {_112000 : Type'} (_60289 : _112000 -> Prop) (P : type686 _112000) (_60290 : _112000 -> Prop) : term147 _112000 _60289 P _60290.
Proof. exact (EQ_MP (@lem4873989 _112000 _60289 P _60290) (@lem4873968 _112000 _60290 P _60289)). Qed.
Lemma lem4873994 {_112000 : Type'} (_60289 : _112000 -> Prop) (P : type686 _112000) (_60290 : _112000 -> Prop) : term147 _112000 _60289 P _60290.
Proof. exact (@lem4873993 _112000 _60289 P _60290). Qed.
Lemma lem4873995 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : term149 _112000 P s.
Proof. exact (@lem4873994 _112000 (term1 _112000 s) P s). Qed.
Lemma lem4873998 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) (h1 : term7 _112000) (h2 : term65 _112000 P s) : P s.
Proof. exact (@lem4873995 _112000 P s (@lem4873991 _112000 P s h1 h2)). Qed.
Lemma lem4873999 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) (h1 : term7 _112000) (h2 : term65 _112000 P s) : term150 _112000 P s.
Proof. exact (fun h0 : term39 _112000 P s => @lem4873998 _112000 P s h1 h2). Qed.
Lemma lem4874001 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4874002 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (term150 _112000 P s) = (P s).
Proof. exact (@lem4874001 (P s)). Qed.
Lemma lem4874003 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) (h1 : term7 _112000) (h2 : term65 _112000 P s) : P s.
Proof. exact (EQ_MP (@lem4874002 _112000 P s) (@lem4873999 _112000 P s h1 h2)). Qed.
Lemma lem4874006 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4874008 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (term39 _112000 P s) = (term151 _112000 P s).
Proof. exact (@lem4874006 (P s)). Qed.
Lemma lem4874011 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) (h1 : term65 _112000 P s) : term151 _112000 P s.
Proof. exact (EQ_MP (@lem4874008 _112000 P s) (@lem4873828 _112000 P s h1)). Qed.
Lemma lem4874014 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) (h1 : term7 _112000) (h2 : term65 _112000 P s) : False.
Proof. exact (@lem4874011 _112000 P s h2 (@lem4874003 _112000 P s h1 h2)). Qed.
Lemma lem4874015 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) (h1 : term7 _112000) (h2 : term65 _112000 P s) : term152.
Proof. exact (fun h0 : ~ False => @lem4874014 _112000 P s h1 h2). Qed.
Lemma lem4874017 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4874018 : term152 = False.
Proof. exact (@lem4874017 False). Qed.
Lemma lem4874019 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) (h1 : term7 _112000) (h2 : term65 _112000 P s) : False.
Proof. exact (EQ_MP (@lem4874018) (@lem4874015 _112000 P s h1 h2)). Qed.
Lemma lem4874050 {_112000 : Type'} (_60288 : _112000 -> Prop) (s : _112000 -> Prop) (P : type686 _112000) (h1 : term85 _112000 s P) : P _60288.
Proof. exact (EQ_MP (@lem4873821 _112000 P _60288) (@lem4873820 _112000 _60288 s P h1)). Qed.
Lemma lem4874051 {_112000 : Type'} (_60288 : _112000 -> Prop) (s : _112000 -> Prop) (P : type686 _112000) (h1 : term85 _112000 s P) : P _60288.
Proof. exact (@lem4874050 _112000 _60288 s P h1). Qed.
Lemma lem4874052 {_112000 : Type'} (s : _112000 -> Prop) (P : type686 _112000) (h1 : term85 _112000 s P) : term22 _112000 P s.
Proof. exact (@lem4874051 _112000 (@DIFF _112000 (@UNIV _112000) s) s P h1). Qed.
Lemma lem4874053 {_112000 : Type'} (s : _112000 -> Prop) (P : type686 _112000) (h1 : term85 _112000 s P) : term153 _112000 P s.
Proof. exact (fun h0 : term31 _112000 P s => @lem4874052 _112000 s P h1). Qed.
Lemma lem4874055 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4874056 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (term153 _112000 P s) = (term22 _112000 P s).
Proof. exact (@lem4874055 (term22 _112000 P s)). Qed.
Lemma lem4874057 {_112000 : Type'} (s : _112000 -> Prop) (P : type686 _112000) (h1 : term85 _112000 s P) : term22 _112000 P s.
Proof. exact (EQ_MP (@lem4874056 _112000 P s) (@lem4874053 _112000 s P h1)). Qed.
Lemma lem4874060 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4874062 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) : (term31 _112000 P s) = (term154 _112000 P s).
Proof. exact (@lem4874060 (term22 _112000 P s)). Qed.
Lemma lem4874065 {_112000 : Type'} (s : _112000 -> Prop) (P : type686 _112000) (h1 : term85 _112000 s P) : term154 _112000 P s.
Proof. exact (EQ_MP (@lem4874062 _112000 P s) (@lem4873832 _112000 s P h1)). Qed.
Lemma lem4874068 {_112000 : Type'} (s : _112000 -> Prop) (P : type686 _112000) (h1 : term85 _112000 s P) : False.
Proof. exact (@lem4874065 _112000 s P h1 (@lem4874057 _112000 s P h1)). Qed.
Lemma lem4874069 {_112000 : Type'} (s : _112000 -> Prop) (P : type686 _112000) (h1 : term85 _112000 s P) : term152.
Proof. exact (fun h0 : ~ False => @lem4874068 _112000 s P h1). Qed.
Lemma lem4874071 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4874072 : term152 = False.
Proof. exact (@lem4874071 False). Qed.
Lemma lem4874073 {_112000 : Type'} (s : _112000 -> Prop) (P : type686 _112000) (h1 : term85 _112000 s P) : False.
Proof. exact (EQ_MP (@lem4874072) (@lem4874069 _112000 s P h1)). Qed.
Lemma lem4874074 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) (h1 : term7 _112000) (h2 : term65 _112000 P s) : (term7 _112000) = False.
Proof. exact (prop_ext (fun h3 : term7 _112000 => @lem4874019 _112000 P s h1 h2) (fun h3 : False => @lem4873781 _112000 h1)). Qed.
Lemma lem4874075 {_112000 : Type'} (P : type686 _112000) (s : _112000 -> Prop) (h1 : term7 _112000) (h2 : term65 _112000 P s) : False.
Proof. exact (EQ_MP (@lem4874074 _112000 P s h1 h2) (@lem4873781 _112000 h1)). Qed.
Lemma lem4874076 {_112000 : Type'} (s : _112000 -> Prop) (P : type686 _112000) (h1 : term7 _112000) (h2 : term108 _112000 s P) : False.
Proof. exact (or_elim (@lem4873768 _112000 s P h2) (fun h0 : term65 _112000 P s => @lem4874075 _112000 P s h1 h0) (fun h0 : term85 _112000 s P => @lem4874073 _112000 s P h0)). Qed.
Lemma lem4874077 {_112000 : Type'} (s : _112000 -> Prop) (P : type686 _112000) (h1 : term7 _112000) (h2 : term108 _112000 s P) : (term108 _112000 s P) = False.
Proof. exact (prop_ext (fun h3 : term108 _112000 s P => @lem4874076 _112000 s P h1 h2) (fun h3 : False => @lem4873768 _112000 s P h2)). Qed.
Lemma lem4874078 {_112000 : Type'} (s : _112000 -> Prop) (P : type686 _112000) (h1 : term7 _112000) (h2 : term108 _112000 s P) : False.
Proof. exact (EQ_MP (@lem4874077 _112000 s P h1 h2) (@lem4873768 _112000 s P h2)). Qed.
Lemma lem4874079 {_112000 : Type'} (s : _112000 -> Prop) (P : type686 _112000) (h1 : term7 _112000) (h2 : term108 _112000 s P) : (term7 _112000) = False.
Proof. exact (prop_ext (fun h3 : term7 _112000 => @lem4874078 _112000 s P h1 h2) (fun h3 : False => @lem4873728 _112000 h1)). Qed.
Lemma lem4874080 {_112000 : Type'} (s : _112000 -> Prop) (P : type686 _112000) (h1 : term7 _112000) (h2 : term108 _112000 s P) : False.
Proof. exact (EQ_MP (@lem4874079 _112000 s P h1 h2) (@lem4873728 _112000 h1)). Qed.
Lemma lem4874081 {_112000 : Type'} (P : type686 _112000) (h1 : term7 _112000) (h2 : term6 _112000 P) : False.
Proof. exact (ex_elim (@lem4873697 _112000 P h2) (fun s : _112000 -> Prop => fun h0 : term110 _112000 P s => @lem4874080 _112000 s P h1 h0)). Qed.
Lemma lem4874082 {_112000 : Type'} (P : type686 _112000) (h1 : term7 _112000) (h2 : term6 _112000 P) : (term7 _112000) = False.
Proof. exact (prop_ext (fun h3 : term7 _112000 => @lem4874081 _112000 P h1 h2) (fun h3 : False => @lem4873710 _112000 h1)). Qed.
Lemma lem4874083 {_112000 : Type'} (P : type686 _112000) (h1 : term7 _112000) (h2 : term6 _112000 P) : False.
Proof. exact (EQ_MP (@lem4874082 _112000 P h1 h2) (@lem4873710 _112000 h1)). Qed.
Lemma lem4874084 {_112000 : Type'} (P : type686 _112000) (h1 : term6 _112000 P) : term12 _112000.
Proof. exact (fun h0 : term7 _112000 => @lem4874083 _112000 P h0 h1). Qed.
Lemma lem4874085 {_112000 : Type'} : (term12 _112000) = (term13 _112000).
Proof. exact (@lem69 (term7 _112000)). Qed.
Lemma lem4874086 {_112000 : Type'} (P : type686 _112000) (h1 : term6 _112000 P) : term13 _112000.
Proof. exact (EQ_MP (@lem4874085 _112000) (@lem4874084 _112000 P h1)). Qed.
Lemma lem4874087 {_112000 : Type'} (P : type686 _112000) : term15 _112000 P.
Proof. exact (fun h0 : term6 _112000 P => @lem4874086 _112000 P h0). Qed.
Lemma lem4874092 {_112000 : Type'} : term19 _112000.
Proof. exact (fun P : type686 _112000 => @lem4874087 _112000 P). Qed.
Lemma lem4874093 {_112000 : Type'} : term18 _112000.
Proof. exact (EQ_MP (@lem4873559 _112000) (@lem4874092 _112000)). Qed.
Lemma lem4874094 {_112000 : Type'} (P : type686 _112000) : term155 _112000 P.
Proof. exact (@lem4874093 _112000 P). Qed.
Lemma lem4874095 {_112000 : Type'} (P : type686 _112000) : (term155 _112000 P) = (term8 _112000 P).
Proof. exact (eq_refl (term155 _112000 P)). Qed.
Lemma lem4874096 {_112000 : Type'} (P : type686 _112000) : term8 _112000 P.
Proof. exact (EQ_MP (@lem4874095 _112000 P) (@lem4874094 _112000 P)). Qed.
Lemma lem4874098 {_112000 : Type'} (P : type686 _112000) : term8 _112000 P.
Proof. exact (@lem4873468 _112000 P (@lem4874096 _112000 P)). Qed.
Lemma lem4874099 {_112000 : Type'} (P : type686 _112000) (h1 : term6 _112000 P) : term12 _112000.
Proof. exact (@lem4874098 _112000 P (@lem4873450 _112000 P h1)). Qed.
Lemma lem4874100 {_112000 : Type'} (P : type686 _112000) (h1 : term6 _112000 P) : False.
Proof. exact (@lem4874099 _112000 P h1 (@lem4873451 _112000)). Qed.
Lemma lem4874101 {_112000 : Type'} (P : type686 _112000) (h1 : term6 _112000 P) : (term6 _112000 P) = False.
Proof. exact (prop_ext (fun h2 : term6 _112000 P => @lem4874100 _112000 P h1) (fun h2 : False => @lem4873450 _112000 P h1)). Qed.
Lemma lem4874102 {_112000 : Type'} (P : type686 _112000) (h1 : term6 _112000 P) : False.
Proof. exact (EQ_MP (@lem4874101 _112000 P h1) (@lem4873450 _112000 P h1)). Qed.
Lemma lem4874103 {_112000 : Type'} (P : type686 _112000) : term5 _112000 P.
Proof. exact (fun h0 : term6 _112000 P => @lem4874102 _112000 P h0). Qed.
Lemma lem4874118 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term156 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4874119 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) : (s = t) = (term156 _112027 s t).
Proof. exact (@lem4874118 _112027 s t). Qed.
Lemma lem4874120 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) : ((term229 _112027 s t) = (term230 _112027 s t)) = (term231 _112027 s t).
Proof. exact (@lem4874119 _112027 (term229 _112027 s t) (term230 _112027 s t)). Qed.
Lemma lem4874129 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) : (term231 _112027 s t) = ((term229 _112027 s t) = (term230 _112027 s t)).
Proof. exact (SYM (@lem4874120 _112027 s t)). Qed.
Lemma lem4874137 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term166 A x s t) = (term167 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem4874138 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) (t : _112027 -> Prop) : (term166 _112027 x s t) = (term167 _112027 s x t).
Proof. exact (@lem4874137 _112027 s x t). Qed.
Lemma lem4874139 {_112027 : Type'} (x : _112027) (s : _112027 -> Prop) (t : _112027 -> Prop) : (term232 _112027 x s t) = (term233 _112027 x s t).
Proof. exact (@lem4874138 _112027 (@UNIV _112027) x (@UNION _112027 s t)). Qed.
Lemma lem4874143 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem4874144 {_112027 : Type'} (x : _112027) : (@IN _112027 x (@UNIV _112027)) = True.
Proof. exact (@lem4874143 _112027 x). Qed.
Lemma lem4874145 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4874146 {_112027 : Type'} (x : _112027) : (term171 _112027 x) = (and True).
Proof. exact (MK_COMB (@lem4874145) (@lem4874144 _112027 x)). Qed.
Lemma lem4874148 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term172 A x s t) = (term173 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem4874149 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) (t : _112027 -> Prop) : (term172 _112027 x s t) = (term173 _112027 s x t).
Proof. exact (@lem4874148 _112027 s x t). Qed.
Lemma lem4874153 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4874154 {_112027 : Type'} (P : _112027 -> Prop) (x : _112027) : (@IN _112027 x P) = (P x).
Proof. exact (@lem4874153 _112027 P x). Qed.
Lemma lem4874155 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) : (@IN _112027 x s) = (s x).
Proof. exact (@lem4874154 _112027 s x). Qed.
Lemma lem4874156 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4874157 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) : (term234 _112027 x s) = (term235 _112027 s x).
Proof. exact (MK_COMB (@lem4874156) (@lem4874155 _112027 s x)). Qed.
Lemma lem4874159 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4874160 {_112027 : Type'} (P : _112027 -> Prop) (x : _112027) : (@IN _112027 x P) = (P x).
Proof. exact (@lem4874159 _112027 P x). Qed.
Lemma lem4874161 {_112027 : Type'} (t : _112027 -> Prop) (x : _112027) : (@IN _112027 x t) = (t x).
Proof. exact (@lem4874160 _112027 t x). Qed.
Lemma lem4874162 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : (term173 _112027 s x t) = (term236 _112027 s t x).
Proof. exact (MK_COMB (@lem4874157 _112027 s x) (@lem4874161 _112027 t x)). Qed.
Lemma lem4874165 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : (term172 _112027 x s t) = (term236 _112027 s t x).
Proof. exact (TRANS (@lem4874149 _112027 s x t) (@lem4874162 _112027 s t x)). Qed.
Lemma lem4874166 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4874167 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : (term237 _112027 x s t) = (term238 _112027 s t x).
Proof. exact (MK_COMB (@lem4874166) (@lem4874165 _112027 s t x)). Qed.
Lemma lem4874168 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : (term233 _112027 x s t) = (term239 _112027 s t x).
Proof. exact (MK_COMB (@lem4874146 _112027 x) (@lem4874167 _112027 s t x)). Qed.
Lemma lem4874170 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4874171 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : (term239 _112027 s t x) = (term238 _112027 s t x).
Proof. exact (@lem4874170 (term238 _112027 s t x)). Qed.
Lemma lem4874174 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : (term233 _112027 x s t) = (term238 _112027 s t x).
Proof. exact (TRANS (@lem4874168 _112027 s t x) (@lem4874171 _112027 s t x)). Qed.
Lemma lem4874175 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : (term232 _112027 x s t) = (term238 _112027 s t x).
Proof. exact (TRANS (@lem4874139 _112027 x s t) (@lem4874174 _112027 s t x)). Qed.
Lemma lem4874176 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4874177 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : (term240 _112027 x s t) = (term241 _112027 s t x).
Proof. exact (MK_COMB (@lem4874176) (@lem4874175 _112027 s t x)). Qed.
Lemma lem4874179 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term159 A x s t) = (term160 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem4874180 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) (t : _112027 -> Prop) : (term159 _112027 x s t) = (term160 _112027 s x t).
Proof. exact (@lem4874179 _112027 s x t). Qed.
Lemma lem4874181 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) (t : _112027 -> Prop) : (term242 _112027 x s t) = (term243 _112027 s x t).
Proof. exact (@lem4874180 _112027 (@DIFF _112027 (@UNIV _112027) s) x (@DIFF _112027 (@UNIV _112027) t)). Qed.
Lemma lem4874185 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term166 A x s t) = (term167 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem4874186 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) (t : _112027 -> Prop) : (term166 _112027 x s t) = (term167 _112027 s x t).
Proof. exact (@lem4874185 _112027 s x t). Qed.
Lemma lem4874187 {_112027 : Type'} (x : _112027) (s : _112027 -> Prop) : (term176 _112027 x s) = (term177 _112027 x s).
Proof. exact (@lem4874186 _112027 (@UNIV _112027) x s). Qed.
Lemma lem4874191 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem4874192 {_112027 : Type'} (x : _112027) : (@IN _112027 x (@UNIV _112027)) = True.
Proof. exact (@lem4874191 _112027 x). Qed.
Lemma lem4874193 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4874194 {_112027 : Type'} (x : _112027) : (term171 _112027 x) = (and True).
Proof. exact (MK_COMB (@lem4874193) (@lem4874192 _112027 x)). Qed.
Lemma lem4874196 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4874197 {_112027 : Type'} (P : _112027 -> Prop) (x : _112027) : (@IN _112027 x P) = (P x).
Proof. exact (@lem4874196 _112027 P x). Qed.
Lemma lem4874198 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) : (@IN _112027 x s) = (s x).
Proof. exact (@lem4874197 _112027 s x). Qed.
Lemma lem4874199 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4874200 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) : (term178 _112027 x s) = (term179 _112027 s x).
Proof. exact (MK_COMB (@lem4874199) (@lem4874198 _112027 s x)). Qed.
Lemma lem4874201 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) : (term177 _112027 x s) = (term180 _112027 s x).
Proof. exact (MK_COMB (@lem4874194 _112027 x) (@lem4874200 _112027 s x)). Qed.
Lemma lem4874203 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4874204 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) : (term180 _112027 s x) = (term179 _112027 s x).
Proof. exact (@lem4874203 (term179 _112027 s x)). Qed.
Lemma lem4874205 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) : (term177 _112027 x s) = (term179 _112027 s x).
Proof. exact (TRANS (@lem4874201 _112027 s x) (@lem4874204 _112027 s x)). Qed.
Lemma lem4874206 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) : (term176 _112027 x s) = (term179 _112027 s x).
Proof. exact (TRANS (@lem4874187 _112027 x s) (@lem4874205 _112027 s x)). Qed.
Lemma lem4874207 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4874208 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) : (term244 _112027 x s) = (term245 _112027 s x).
Proof. exact (MK_COMB (@lem4874207) (@lem4874206 _112027 s x)). Qed.
Lemma lem4874210 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term166 A x s t) = (term167 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem4874211 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) (t : _112027 -> Prop) : (term166 _112027 x s t) = (term167 _112027 s x t).
Proof. exact (@lem4874210 _112027 s x t). Qed.
Lemma lem4874212 {_112027 : Type'} (x : _112027) (t : _112027 -> Prop) : (term176 _112027 x t) = (term177 _112027 x t).
Proof. exact (@lem4874211 _112027 (@UNIV _112027) x t). Qed.
Lemma lem4874216 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem4874217 {_112027 : Type'} (x : _112027) : (@IN _112027 x (@UNIV _112027)) = True.
Proof. exact (@lem4874216 _112027 x). Qed.
Lemma lem4874218 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4874219 {_112027 : Type'} (x : _112027) : (term171 _112027 x) = (and True).
Proof. exact (MK_COMB (@lem4874218) (@lem4874217 _112027 x)). Qed.
Lemma lem4874221 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4874222 {_112027 : Type'} (P : _112027 -> Prop) (x : _112027) : (@IN _112027 x P) = (P x).
Proof. exact (@lem4874221 _112027 P x). Qed.
Lemma lem4874223 {_112027 : Type'} (t : _112027 -> Prop) (x : _112027) : (@IN _112027 x t) = (t x).
Proof. exact (@lem4874222 _112027 t x). Qed.
Lemma lem4874224 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4874225 {_112027 : Type'} (t : _112027 -> Prop) (x : _112027) : (term178 _112027 x t) = (term179 _112027 t x).
Proof. exact (MK_COMB (@lem4874224) (@lem4874223 _112027 t x)). Qed.
Lemma lem4874226 {_112027 : Type'} (t : _112027 -> Prop) (x : _112027) : (term177 _112027 x t) = (term180 _112027 t x).
Proof. exact (MK_COMB (@lem4874219 _112027 x) (@lem4874225 _112027 t x)). Qed.
Lemma lem4874228 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4874229 {_112027 : Type'} (t : _112027 -> Prop) (x : _112027) : (term180 _112027 t x) = (term179 _112027 t x).
Proof. exact (@lem4874228 (term179 _112027 t x)). Qed.
Lemma lem4874230 {_112027 : Type'} (t : _112027 -> Prop) (x : _112027) : (term177 _112027 x t) = (term179 _112027 t x).
Proof. exact (TRANS (@lem4874226 _112027 t x) (@lem4874229 _112027 t x)). Qed.
Lemma lem4874231 {_112027 : Type'} (t : _112027 -> Prop) (x : _112027) : (term176 _112027 x t) = (term179 _112027 t x).
Proof. exact (TRANS (@lem4874212 _112027 x t) (@lem4874230 _112027 t x)). Qed.
Lemma lem4874232 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : (term243 _112027 s x t) = (term246 _112027 s t x).
Proof. exact (MK_COMB (@lem4874208 _112027 s x) (@lem4874231 _112027 t x)). Qed.
Lemma lem4874235 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : (term242 _112027 x s t) = (term246 _112027 s t x).
Proof. exact (TRANS (@lem4874181 _112027 s x t) (@lem4874232 _112027 s t x)). Qed.
Lemma lem4874236 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : ((term232 _112027 x s t) = (term242 _112027 x s t)) = ((term238 _112027 s t x) = (term246 _112027 s t x)).
Proof. exact (MK_COMB (@lem4874177 _112027 s t x) (@lem4874235 _112027 s t x)). Qed.
Lemma lem4874239 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) : (term247 _112027 s t) = (term248 _112027 s t).
Proof. exact (fun_ext (fun x : _112027 => @lem4874236 _112027 s t x)). Qed.
Lemma lem4874240 {_112027 : Type'} : (@all _112027) = (@all _112027).
Proof. exact (eq_refl (@all _112027)). Qed.
Lemma lem4874241 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) : (term231 _112027 s t) = (term249 _112027 s t).
Proof. exact (MK_COMB (@lem4874240 _112027) (@lem4874239 _112027 s t)). Qed.
Lemma lem4874246 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) : (term249 _112027 s t) = (term231 _112027 s t).
Proof. exact (SYM (@lem4874241 _112027 s t)). Qed.
Lemma lem4874248 (p : Prop) : p = (term2 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4874249 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) : (term249 _112027 s t) = (term250 _112027 s t).
Proof. exact (@lem4874248 (term249 _112027 s t)). Qed.
Lemma lem4874250 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) : (term250 _112027 s t) = (term249 _112027 s t).
Proof. exact (SYM (@lem4874249 _112027 s t)). Qed.
Lemma lem4874251 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (h1 : term251 _112027 s t) : term251 _112027 s t.
Proof. exact (h1). Qed.
Lemma lem4874254 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (h1 : term250 _112027 s t) : term250 _112027 s t.
Proof. exact (h1). Qed.
Lemma lem4874255 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) : term252 _112027 s t.
Proof. exact (fun h0 : term250 _112027 s t => @lem4874254 _112027 s t h0). Qed.
Lemma lem4874256 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (h1 : term252 _112027 s t) : term252 _112027 s t.
Proof. exact (h1). Qed.
Lemma lem4874257 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (h1 : term250 _112027 s t) : term250 _112027 s t.
Proof. exact (h1). Qed.
Lemma lem4874258 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (h1 : term250 _112027 s t) (h2 : term252 _112027 s t) : term250 _112027 s t.
Proof. exact (@lem4874256 _112027 s t h2 (@lem4874257 _112027 s t h1)). Qed.
Lemma lem4874259 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (h1 : term250 _112027 s t) : term253 _112027 s t.
Proof. exact (fun h0 : term252 _112027 s t => @lem4874258 _112027 s t h1 h0). Qed.
Lemma lem4874260 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (h1 : term252 _112027 s t) : term252 _112027 s t.
Proof. exact (h1). Qed.
Lemma lem4874261 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (h1 : term250 _112027 s t) (h2 : term252 _112027 s t) : term250 _112027 s t.
Proof. exact (@lem4874259 _112027 s t h1 (@lem4874260 _112027 s t h2)). Qed.
Lemma lem4874262 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (h1 : term252 _112027 s t) : term252 _112027 s t.
Proof. exact (fun h0 : term250 _112027 s t => @lem4874261 _112027 s t h0 h1). Qed.
Lemma lem4874263 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) : term254 _112027 s t.
Proof. exact (fun h0 : term252 _112027 s t => @lem4874262 _112027 s t h0). Qed.
Lemma lem4874266 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) : term252 _112027 s t.
Proof. exact (@lem4874263 _112027 s t (@lem4874255 _112027 s t)). Qed.
Lemma lem4874267 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) : term252 _112027 s t.
Proof. exact (@lem4874266 _112027 s t). Qed.
Lemma lem4874277 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4874278 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) : (term250 _112027 s t) = (term255 _112027 s t).
Proof. exact (@lem4874277 (term251 _112027 s t)). Qed.
Lemma lem4874280 (t : Prop) : (term139 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4874281 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) : (term255 _112027 s t) = (term249 _112027 s t).
Proof. exact (@lem4874280 (term249 _112027 s t)). Qed.
Lemma lem4874286 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) : (term250 _112027 s t) = (term249 _112027 s t).
Proof. exact (TRANS (@lem4874278 _112027 s t) (@lem4874281 _112027 s t)). Qed.
Lemma lem4874291 {_112027 : Type'} (t : _112027 -> Prop) : (term256 _112027 t) = (term257 _112027 t).
Proof. exact (fun_ext (fun s : _112027 -> Prop => @lem4874286 _112027 s t)). Qed.
Lemma lem4874292 {_112027 : Type'} : (@all (_112027 -> Prop)) = (@all (_112027 -> Prop)).
Proof. exact (eq_refl (@all (_112027 -> Prop))). Qed.
Lemma lem4874293 {_112027 : Type'} (t : _112027 -> Prop) : (term258 _112027 t) = (term259 _112027 t).
Proof. exact (MK_COMB (@lem4874292 _112027) (@lem4874291 _112027 t)). Qed.
Lemma lem4874298 {_112027 : Type'} : (term260 _112027) = (term261 _112027).
Proof. exact (fun_ext (fun t : _112027 -> Prop => @lem4874293 _112027 t)). Qed.
Lemma lem4874299 {_112027 : Type'} : (@all (_112027 -> Prop)) = (@all (_112027 -> Prop)).
Proof. exact (eq_refl (@all (_112027 -> Prop))). Qed.
Lemma lem4874308 {_112027 : Type'} : (term262 _112027) = (term263 _112027).
Proof. exact (MK_COMB (@lem4874299 _112027) (@lem4874298 _112027)). Qed.
Lemma lem4874327 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : ((term238 _112027 s t x) = (term246 _112027 s t x)) = ((term238 _112027 s t x) = (term246 _112027 s t x)).
Proof. exact (eq_refl ((term238 _112027 s t x) = (term246 _112027 s t x))). Qed.
Lemma lem4874328 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) : (term248 _112027 s t) = (term248 _112027 s t).
Proof. exact (fun_ext (fun x : _112027 => @lem4874327 _112027 s t x)). Qed.
Lemma lem4874329 {_112027 : Type'} : (@all _112027) = (@all _112027).
Proof. exact (eq_refl (@all _112027)). Qed.
Lemma lem4874330 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) : (term249 _112027 s t) = (term249 _112027 s t).
Proof. exact (MK_COMB (@lem4874329 _112027) (@lem4874328 _112027 s t)). Qed.
Lemma lem4874331 {_112027 : Type'} (t : _112027 -> Prop) : (term257 _112027 t) = (term257 _112027 t).
Proof. exact (fun_ext (fun s : _112027 -> Prop => @lem4874330 _112027 s t)). Qed.
Lemma lem4874332 {_112027 : Type'} : (@all (_112027 -> Prop)) = (@all (_112027 -> Prop)).
Proof. exact (eq_refl (@all (_112027 -> Prop))). Qed.
Lemma lem4874333 {_112027 : Type'} (t : _112027 -> Prop) : (term259 _112027 t) = (term259 _112027 t).
Proof. exact (MK_COMB (@lem4874332 _112027) (@lem4874331 _112027 t)). Qed.
Lemma lem4874334 {_112027 : Type'} : (term261 _112027) = (term261 _112027).
Proof. exact (fun_ext (fun t : _112027 -> Prop => @lem4874333 _112027 t)). Qed.
Lemma lem4874335 {_112027 : Type'} : (@all (_112027 -> Prop)) = (@all (_112027 -> Prop)).
Proof. exact (eq_refl (@all (_112027 -> Prop))). Qed.
Lemma lem4874336 {_112027 : Type'} : (term263 _112027) = (term263 _112027).
Proof. exact (MK_COMB (@lem4874335 _112027) (@lem4874334 _112027)). Qed.
Lemma lem4874361 {_112027 : Type'} : (term262 _112027) = (term263 _112027).
Proof. exact (TRANS (@lem4874308 _112027) (@lem4874336 _112027)). Qed.
Lemma lem4874362 {_112027 : Type'} : (term263 _112027) = (term262 _112027).
Proof. exact (SYM (@lem4874361 _112027)). Qed.
Lemma lem4874364 (p : Prop) : p = (term2 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4874365 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : ((term238 _112027 s t x) = (term246 _112027 s t x)) = (term264 _112027 s t x).
Proof. exact (@lem4874364 ((term238 _112027 s t x) = (term246 _112027 s t x))). Qed.
Lemma lem4874366 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : (term264 _112027 s t x) = ((term238 _112027 s t x) = (term246 _112027 s t x)).
Proof. exact (SYM (@lem4874365 _112027 s t x)). Qed.
Lemma lem4874367 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : term265 _112027 s t x) : term265 _112027 s t x.
Proof. exact (h1). Qed.
Lemma lem4874376 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : (term238 _112027 s t x) = (term246 _112027 s t x).
Proof. exact (@lem17160 (s x) (t x)). Qed.
Lemma lem4874381 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : (term266 _112027 s t x) = (term236 _112027 s t x).
Proof. exact (@lem16933 (term236 _112027 s t x)). Qed.
Lemma lem4874385 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) : (term207 _112027 s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem4874389 {_112027 : Type'} (t : _112027 -> Prop) (x : _112027) : (term207 _112027 t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem4874390 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4874391 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) : (term267 _112027 s x) = (term235 _112027 s x).
Proof. exact (MK_COMB (@lem4874390) (@lem4874385 _112027 s x)). Qed.
Lemma lem4874392 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : (term268 _112027 s t x) = (term236 _112027 s t x).
Proof. exact (MK_COMB (@lem4874391 _112027 s x) (@lem4874389 _112027 t x)). Qed.
Lemma lem4874393 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : (term269 _112027 s t x) = (term268 _112027 s t x).
Proof. exact (@lem17045 (term179 _112027 s x) (term179 _112027 t x)). Qed.
Lemma lem4874394 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : (term269 _112027 s t x) = (term236 _112027 s t x).
Proof. exact (TRANS (@lem4874393 _112027 s t x) (@lem4874392 _112027 s t x)). Qed.
Lemma lem4874397 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : (term246 _112027 s t x) = (term246 _112027 s t x).
Proof. exact (eq_refl (term246 _112027 s t x)). Qed.
Lemma lem4874398 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4874399 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : (term270 _112027 s t x) = (term271 _112027 s t x).
Proof. exact (MK_COMB (@lem4874398) (@lem4874381 _112027 s t x)). Qed.
Lemma lem4874400 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : (term272 _112027 s t x) = (term273 _112027 s t x).
Proof. exact (MK_COMB (@lem4874399 _112027 s t x) (@lem4874397 _112027 s t x)). Qed.
Lemma lem4874401 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4874402 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : (term274 _112027 s t x) = (term275 _112027 s t x).
Proof. exact (MK_COMB (@lem4874401) (@lem4874376 _112027 s t x)). Qed.
Lemma lem4874403 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : (term276 _112027 s t x) = (term277 _112027 s t x).
Proof. exact (MK_COMB (@lem4874402 _112027 s t x) (@lem4874394 _112027 s t x)). Qed.
Lemma lem4874404 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4874405 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : (term278 _112027 s t x) = (term279 _112027 s t x).
Proof. exact (MK_COMB (@lem4874404) (@lem4874403 _112027 s t x)). Qed.
Lemma lem4874406 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : (term280 _112027 s t x) = (term281 _112027 s t x).
Proof. exact (MK_COMB (@lem4874405 _112027 s t x) (@lem4874400 _112027 s t x)). Qed.
Lemma lem4874407 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : (term265 _112027 s t x) = (term280 _112027 s t x).
Proof. exact (@lem17646 (term238 _112027 s t x) (term246 _112027 s t x)). Qed.
Lemma lem4874412 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : (term265 _112027 s t x) = (term281 _112027 s t x).
Proof. exact (TRANS (@lem4874407 _112027 s t x) (@lem4874406 _112027 s t x)). Qed.
Lemma lem4874467 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : term265 _112027 s t x) : term281 _112027 s t x.
Proof. exact (EQ_MP (@lem4874412 _112027 s t x) (@lem4874367 _112027 s t x h1)). Qed.
Lemma lem4874468 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : term277 _112027 s t x) : term277 _112027 s t x.
Proof. exact (h1). Qed.
Lemma lem4874469 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : term273 _112027 s t x) : term273 _112027 s t x.
Proof. exact (h1). Qed.
Lemma lem4874470 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : term277 _112027 s t x) : term236 _112027 s t x.
Proof. exact (proj2 (@lem4874468 _112027 s t x h1)). Qed.
Lemma lem4874471 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : term277 _112027 s t x) : term246 _112027 s t x.
Proof. exact (proj1 (@lem4874468 _112027 s t x h1)). Qed.
Lemma lem4874476 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : term273 _112027 s t x) : term246 _112027 s t x.
Proof. exact (proj2 (@lem4874469 _112027 s t x h1)). Qed.
Lemma lem4874477 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : term273 _112027 s t x) : term236 _112027 s t x.
Proof. exact (proj1 (@lem4874469 _112027 s t x h1)). Qed.
Lemma lem4874493 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem4874505 {_112027 : Type'} (t : _112027 -> Prop) (x : _112027) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4874517 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem4874529 {_112027 : Type'} (t : _112027 -> Prop) (x : _112027) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4874531 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : term277 _112027 s t x) : term179 _112027 s x.
Proof. exact (proj1 (@lem4874471 _112027 s t x h1)). Qed.
Lemma lem4874535 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem4874539 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : term277 _112027 s t x) : term179 _112027 t x.
Proof. exact (proj2 (@lem4874471 _112027 s t x h1)). Qed.
Lemma lem4874541 {_112027 : Type'} (t : _112027 -> Prop) (x : _112027) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4874543 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : term273 _112027 s t x) : term179 _112027 s x.
Proof. exact (proj1 (@lem4874476 _112027 s t x h1)). Qed.
Lemma lem4874547 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem4874551 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : term273 _112027 s t x) : term179 _112027 t x.
Proof. exact (proj2 (@lem4874476 _112027 s t x h1)). Qed.
Lemma lem4874553 {_112027 : Type'} (t : _112027 -> Prop) (x : _112027) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4874555 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem4874556 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) (h1 : s x) : term222 _112027 s x.
Proof. exact (fun h0 : term179 _112027 s x => @lem4874555 _112027 s x h1). Qed.
Lemma lem4874558 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4874559 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) : (term222 _112027 s x) = (s x).
Proof. exact (@lem4874558 (s x)). Qed.
Lemma lem4874560 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem4874559 _112027 s x) (@lem4874556 _112027 s x h1)). Qed.
Lemma lem4874563 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4874565 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) : (term179 _112027 s x) = (term223 _112027 s x).
Proof. exact (@lem4874563 (s x)). Qed.
Lemma lem4874568 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : term277 _112027 s t x) : term223 _112027 s x.
Proof. exact (EQ_MP (@lem4874565 _112027 s x) (@lem4874531 _112027 s t x h1)). Qed.
Lemma lem4874571 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : s x) (h2 : term277 _112027 s t x) : False.
Proof. exact (@lem4874568 _112027 s t x h2 (@lem4874560 _112027 s x h1)). Qed.
Lemma lem4874572 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : s x) (h2 : term277 _112027 s t x) : term152.
Proof. exact (fun h0 : ~ False => @lem4874571 _112027 s t x h1 h2). Qed.
Lemma lem4874574 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4874575 : term152 = False.
Proof. exact (@lem4874574 False). Qed.
Lemma lem4874576 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : s x) (h2 : term277 _112027 s t x) : False.
Proof. exact (EQ_MP (@lem4874575) (@lem4874572 _112027 s t x h1 h2)). Qed.
Lemma lem4874578 {_112027 : Type'} (t : _112027 -> Prop) (x : _112027) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4874579 {_112027 : Type'} (t : _112027 -> Prop) (x : _112027) (h1 : t x) : term222 _112027 t x.
Proof. exact (fun h0 : term179 _112027 t x => @lem4874578 _112027 t x h1). Qed.
Lemma lem4874581 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4874582 {_112027 : Type'} (t : _112027 -> Prop) (x : _112027) : (term222 _112027 t x) = (t x).
Proof. exact (@lem4874581 (t x)). Qed.
Lemma lem4874583 {_112027 : Type'} (t : _112027 -> Prop) (x : _112027) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem4874582 _112027 t x) (@lem4874579 _112027 t x h1)). Qed.
Lemma lem4874586 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4874588 {_112027 : Type'} (t : _112027 -> Prop) (x : _112027) : (term179 _112027 t x) = (term223 _112027 t x).
Proof. exact (@lem4874586 (t x)). Qed.
Lemma lem4874591 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : term277 _112027 s t x) : term223 _112027 t x.
Proof. exact (EQ_MP (@lem4874588 _112027 t x) (@lem4874539 _112027 s t x h1)). Qed.
Lemma lem4874594 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : t x) (h2 : term277 _112027 s t x) : False.
Proof. exact (@lem4874591 _112027 s t x h2 (@lem4874583 _112027 t x h1)). Qed.
Lemma lem4874595 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : t x) (h2 : term277 _112027 s t x) : term152.
Proof. exact (fun h0 : ~ False => @lem4874594 _112027 s t x h1 h2). Qed.
Lemma lem4874597 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4874598 : term152 = False.
Proof. exact (@lem4874597 False). Qed.
Lemma lem4874599 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : t x) (h2 : term277 _112027 s t x) : False.
Proof. exact (EQ_MP (@lem4874598) (@lem4874595 _112027 s t x h1 h2)). Qed.
Lemma lem4874601 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem4874602 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) (h1 : s x) : term222 _112027 s x.
Proof. exact (fun h0 : term179 _112027 s x => @lem4874601 _112027 s x h1). Qed.
Lemma lem4874604 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4874605 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) : (term222 _112027 s x) = (s x).
Proof. exact (@lem4874604 (s x)). Qed.
Lemma lem4874606 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem4874605 _112027 s x) (@lem4874602 _112027 s x h1)). Qed.
Lemma lem4874609 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4874611 {_112027 : Type'} (s : _112027 -> Prop) (x : _112027) : (term179 _112027 s x) = (term223 _112027 s x).
Proof. exact (@lem4874609 (s x)). Qed.
Lemma lem4874614 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : term273 _112027 s t x) : term223 _112027 s x.
Proof. exact (EQ_MP (@lem4874611 _112027 s x) (@lem4874543 _112027 s t x h1)). Qed.
Lemma lem4874617 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : s x) (h2 : term273 _112027 s t x) : False.
Proof. exact (@lem4874614 _112027 s t x h2 (@lem4874606 _112027 s x h1)). Qed.
Lemma lem4874618 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : s x) (h2 : term273 _112027 s t x) : term152.
Proof. exact (fun h0 : ~ False => @lem4874617 _112027 s t x h1 h2). Qed.
Lemma lem4874620 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4874621 : term152 = False.
Proof. exact (@lem4874620 False). Qed.
Lemma lem4874622 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : s x) (h2 : term273 _112027 s t x) : False.
Proof. exact (EQ_MP (@lem4874621) (@lem4874618 _112027 s t x h1 h2)). Qed.
Lemma lem4874624 {_112027 : Type'} (t : _112027 -> Prop) (x : _112027) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4874625 {_112027 : Type'} (t : _112027 -> Prop) (x : _112027) (h1 : t x) : term222 _112027 t x.
Proof. exact (fun h0 : term179 _112027 t x => @lem4874624 _112027 t x h1). Qed.
Lemma lem4874627 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4874628 {_112027 : Type'} (t : _112027 -> Prop) (x : _112027) : (term222 _112027 t x) = (t x).
Proof. exact (@lem4874627 (t x)). Qed.
Lemma lem4874629 {_112027 : Type'} (t : _112027 -> Prop) (x : _112027) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem4874628 _112027 t x) (@lem4874625 _112027 t x h1)). Qed.
Lemma lem4874632 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4874634 {_112027 : Type'} (t : _112027 -> Prop) (x : _112027) : (term179 _112027 t x) = (term223 _112027 t x).
Proof. exact (@lem4874632 (t x)). Qed.
Lemma lem4874637 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : term273 _112027 s t x) : term223 _112027 t x.
Proof. exact (EQ_MP (@lem4874634 _112027 t x) (@lem4874551 _112027 s t x h1)). Qed.
Lemma lem4874640 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : t x) (h2 : term273 _112027 s t x) : False.
Proof. exact (@lem4874637 _112027 s t x h2 (@lem4874629 _112027 t x h1)). Qed.
Lemma lem4874641 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : t x) (h2 : term273 _112027 s t x) : term152.
Proof. exact (fun h0 : ~ False => @lem4874640 _112027 s t x h1 h2). Qed.
Lemma lem4874643 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4874644 : term152 = False.
Proof. exact (@lem4874643 False). Qed.
Lemma lem4874645 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : t x) (h2 : term273 _112027 s t x) : False.
Proof. exact (EQ_MP (@lem4874644) (@lem4874641 _112027 s t x h1 h2)). Qed.
Lemma lem4874646 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : t x) (h2 : term273 _112027 s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem4874645 _112027 s t x h1 h2) (fun h3 : False => @lem4874553 _112027 t x h1)). Qed.
Lemma lem4874647 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : t x) (h2 : term273 _112027 s t x) : False.
Proof. exact (EQ_MP (@lem4874646 _112027 s t x h1 h2) (@lem4874553 _112027 t x h1)). Qed.
Lemma lem4874648 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : s x) (h2 : term273 _112027 s t x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem4874622 _112027 s t x h1 h2) (fun h3 : False => @lem4874547 _112027 s x h1)). Qed.
Lemma lem4874649 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : s x) (h2 : term273 _112027 s t x) : False.
Proof. exact (EQ_MP (@lem4874648 _112027 s t x h1 h2) (@lem4874547 _112027 s x h1)). Qed.
Lemma lem4874650 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : t x) (h2 : term277 _112027 s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem4874599 _112027 s t x h1 h2) (fun h3 : False => @lem4874541 _112027 t x h1)). Qed.
Lemma lem4874651 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : t x) (h2 : term277 _112027 s t x) : False.
Proof. exact (EQ_MP (@lem4874650 _112027 s t x h1 h2) (@lem4874541 _112027 t x h1)). Qed.
Lemma lem4874652 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : s x) (h2 : term277 _112027 s t x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem4874576 _112027 s t x h1 h2) (fun h3 : False => @lem4874535 _112027 s x h1)). Qed.
Lemma lem4874653 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : s x) (h2 : term277 _112027 s t x) : False.
Proof. exact (EQ_MP (@lem4874652 _112027 s t x h1 h2) (@lem4874535 _112027 s x h1)). Qed.
Lemma lem4874654 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : t x) (h2 : term273 _112027 s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem4874647 _112027 s t x h1 h2) (fun h3 : False => @lem4874529 _112027 t x h1)). Qed.
Lemma lem4874655 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : t x) (h2 : term273 _112027 s t x) : False.
Proof. exact (EQ_MP (@lem4874654 _112027 s t x h1 h2) (@lem4874529 _112027 t x h1)). Qed.
Lemma lem4874656 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : s x) (h2 : term273 _112027 s t x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem4874649 _112027 s t x h1 h2) (fun h3 : False => @lem4874517 _112027 s x h1)). Qed.
Lemma lem4874657 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : s x) (h2 : term273 _112027 s t x) : False.
Proof. exact (EQ_MP (@lem4874656 _112027 s t x h1 h2) (@lem4874517 _112027 s x h1)). Qed.
Lemma lem4874658 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : t x) (h2 : term277 _112027 s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem4874651 _112027 s t x h1 h2) (fun h3 : False => @lem4874505 _112027 t x h1)). Qed.
Lemma lem4874659 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : t x) (h2 : term277 _112027 s t x) : False.
Proof. exact (EQ_MP (@lem4874658 _112027 s t x h1 h2) (@lem4874505 _112027 t x h1)). Qed.
Lemma lem4874660 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : s x) (h2 : term277 _112027 s t x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem4874653 _112027 s t x h1 h2) (fun h3 : False => @lem4874493 _112027 s x h1)). Qed.
Lemma lem4874661 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : s x) (h2 : term277 _112027 s t x) : False.
Proof. exact (EQ_MP (@lem4874660 _112027 s t x h1 h2) (@lem4874493 _112027 s x h1)). Qed.
Lemma lem4874662 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : t x) (h2 : term273 _112027 s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem4874655 _112027 s t x h1 h2) (fun h3 : False => @lem4874529 _112027 t x h1)). Qed.
Lemma lem4874663 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : t x) (h2 : term273 _112027 s t x) : False.
Proof. exact (EQ_MP (@lem4874662 _112027 s t x h1 h2) (@lem4874529 _112027 t x h1)). Qed.
Lemma lem4874664 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : s x) (h2 : term273 _112027 s t x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem4874657 _112027 s t x h1 h2) (fun h3 : False => @lem4874517 _112027 s x h1)). Qed.
Lemma lem4874665 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : s x) (h2 : term273 _112027 s t x) : False.
Proof. exact (EQ_MP (@lem4874664 _112027 s t x h1 h2) (@lem4874517 _112027 s x h1)). Qed.
Lemma lem4874666 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : t x) (h2 : term277 _112027 s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem4874659 _112027 s t x h1 h2) (fun h3 : False => @lem4874505 _112027 t x h1)). Qed.
Lemma lem4874667 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : t x) (h2 : term277 _112027 s t x) : False.
Proof. exact (EQ_MP (@lem4874666 _112027 s t x h1 h2) (@lem4874505 _112027 t x h1)). Qed.
Lemma lem4874668 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : s x) (h2 : term277 _112027 s t x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem4874661 _112027 s t x h1 h2) (fun h3 : False => @lem4874493 _112027 s x h1)). Qed.
Lemma lem4874669 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : s x) (h2 : term277 _112027 s t x) : False.
Proof. exact (EQ_MP (@lem4874668 _112027 s t x h1 h2) (@lem4874493 _112027 s x h1)). Qed.
Lemma lem4874670 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : term273 _112027 s t x) : False.
Proof. exact (or_elim (@lem4874477 _112027 s t x h1) (fun h0 : s x => @lem4874665 _112027 s t x h0 h1) (fun h0 : t x => @lem4874663 _112027 s t x h0 h1)). Qed.
Lemma lem4874671 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : term277 _112027 s t x) : False.
Proof. exact (or_elim (@lem4874470 _112027 s t x h1) (fun h0 : s x => @lem4874669 _112027 s t x h0 h1) (fun h0 : t x => @lem4874667 _112027 s t x h0 h1)). Qed.
Lemma lem4874672 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : term265 _112027 s t x) : False.
Proof. exact (or_elim (@lem4874467 _112027 s t x h1) (fun h0 : term277 _112027 s t x => @lem4874671 _112027 s t x h0) (fun h0 : term273 _112027 s t x => @lem4874670 _112027 s t x h0)). Qed.
Lemma lem4874673 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : term265 _112027 s t x) : (term265 _112027 s t x) = False.
Proof. exact (prop_ext (fun h2 : term265 _112027 s t x => @lem4874672 _112027 s t x h1) (fun h2 : False => @lem4874367 _112027 s t x h1)). Qed.
Lemma lem4874674 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) (h1 : term265 _112027 s t x) : False.
Proof. exact (EQ_MP (@lem4874673 _112027 s t x h1) (@lem4874367 _112027 s t x h1)). Qed.
Lemma lem4874675 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : term264 _112027 s t x.
Proof. exact (fun h0 : term265 _112027 s t x => @lem4874674 _112027 s t x h0). Qed.
Lemma lem4874676 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (x : _112027) : (term238 _112027 s t x) = (term246 _112027 s t x).
Proof. exact (EQ_MP (@lem4874366 _112027 s t x) (@lem4874675 _112027 s t x)). Qed.
Lemma lem4874681 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) : term249 _112027 s t.
Proof. exact (fun x : _112027 => @lem4874676 _112027 s t x). Qed.
Lemma lem4874686 {_112027 : Type'} (t : _112027 -> Prop) : term259 _112027 t.
Proof. exact (fun s : _112027 -> Prop => @lem4874681 _112027 s t). Qed.
Lemma lem4874691 {_112027 : Type'} : term263 _112027.
Proof. exact (fun t : _112027 -> Prop => @lem4874686 _112027 t). Qed.
Lemma lem4874692 {_112027 : Type'} : term262 _112027.
Proof. exact (EQ_MP (@lem4874362 _112027) (@lem4874691 _112027)). Qed.
Lemma lem4874693 {_112027 : Type'} (t : _112027 -> Prop) : term282 _112027 t.
Proof. exact (@lem4874692 _112027 t). Qed.
Lemma lem4874694 {_112027 : Type'} (t : _112027 -> Prop) : (term282 _112027 t) = (term258 _112027 t).
Proof. exact (eq_refl (term282 _112027 t)). Qed.
Lemma lem4874695 {_112027 : Type'} (t : _112027 -> Prop) : term258 _112027 t.
Proof. exact (EQ_MP (@lem4874694 _112027 t) (@lem4874693 _112027 t)). Qed.
Lemma lem4874696 {_112027 : Type'} (t : _112027 -> Prop) (s : _112027 -> Prop) : term283 _112027 t s.
Proof. exact (@lem4874695 _112027 t s). Qed.
Lemma lem4874697 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) : (term283 _112027 t s) = (term250 _112027 s t).
Proof. exact (eq_refl (term283 _112027 t s)). Qed.
Lemma lem4874698 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) : term250 _112027 s t.
Proof. exact (EQ_MP (@lem4874697 _112027 s t) (@lem4874696 _112027 t s)). Qed.
Lemma lem4874700 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) : term250 _112027 s t.
Proof. exact (@lem4874267 _112027 s t (@lem4874698 _112027 s t)). Qed.
Lemma lem4874701 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (h1 : term251 _112027 s t) : False.
Proof. exact (@lem4874700 _112027 s t (@lem4874251 _112027 s t h1)). Qed.
Lemma lem4874702 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (h1 : term251 _112027 s t) : (term251 _112027 s t) = False.
Proof. exact (prop_ext (fun h2 : term251 _112027 s t => @lem4874701 _112027 s t h1) (fun h2 : False => @lem4874251 _112027 s t h1)). Qed.
Lemma lem4874703 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) (h1 : term251 _112027 s t) : False.
Proof. exact (EQ_MP (@lem4874702 _112027 s t h1) (@lem4874251 _112027 s t h1)). Qed.
Lemma lem4874704 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) : term250 _112027 s t.
Proof. exact (fun h0 : term251 _112027 s t => @lem4874703 _112027 s t h0). Qed.
Lemma lem4874705 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) : term249 _112027 s t.
Proof. exact (EQ_MP (@lem4874250 _112027 s t) (@lem4874704 _112027 s t)). Qed.
Lemma lem4874706 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) : term231 _112027 s t.
Proof. exact (EQ_MP (@lem4874246 _112027 s t) (@lem4874705 _112027 s t)). Qed.
Lemma lem4874708 {A : Type'} (P : type686 A) : term284 A P.
Proof. exact (@lem4860962 A P). Qed.
Lemma lem4874709 {A : Type'} (P : type686 A) : (term284 A P) = (term285 A P).
Proof. exact (eq_refl (term284 A P)). Qed.
Lemma lem4874710 {A : Type'} (P : type686 A) : term285 A P.
Proof. exact (EQ_MP (@lem4874709 A P) (@lem4874708 A P)). Qed.
Lemma lem4874711 {A : Type'} (P : type686 A) (s : A -> Prop) : term286 A P s.
Proof. exact (@lem4874710 A P s). Qed.
Lemma lem4874712 {A : Type'} (P : type686 A) (s : A -> Prop) : (term286 A P s) = ((@INTERSECTION_OF A (@ARBITRARY A) P s) = (term287 A P s)).
Proof. exact (eq_refl (term286 A P s)). Qed.
Lemma lem4874733 {A : Type'} (P : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A (@ARBITRARY A) P s) = (term287 A P s).
Proof. exact (EQ_MP (@lem4874712 A P s) (@lem4874711 A P s)). Qed.
Lemma lem4874734 {A : Type'} (P : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A (@ARBITRARY A) P s) = (term287 A P s).
Proof. exact (@lem4874733 A P s). Qed.
Lemma lem4874735 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4874736 {A : Type'} (P : type686 A) (s : A -> Prop) : (term288 A P s) = (term289 A P s).
Proof. exact (MK_COMB (@lem4874735) (@lem4874734 A P s)). Qed.
Lemma lem4874738 {A : Type'} (P : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A (@ARBITRARY A) P s) = (term287 A P s).
Proof. exact (EQ_MP (@lem4874712 A P s) (@lem4874711 A P s)). Qed.
Lemma lem4874739 {A : Type'} (P : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A (@ARBITRARY A) P s) = (term287 A P s).
Proof. exact (@lem4874738 A P s). Qed.
Lemma lem4874740 {A : Type'} (P : type686 A) (t : A -> Prop) : (@INTERSECTION_OF A (@ARBITRARY A) P t) = (term287 A P t).
Proof. exact (@lem4874739 A P t). Qed.
Lemma lem4874741 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term290 A s P t) = (term291 A s P t).
Proof. exact (MK_COMB (@lem4874736 A P s) (@lem4874740 A P t)). Qed.
Lemma lem4874742 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4874743 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term292 A s P t) = (term293 A s P t).
Proof. exact (MK_COMB (@lem4874742) (@lem4874741 A s P t)). Qed.
Lemma lem4874745 {A : Type'} (P : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A (@ARBITRARY A) P s) = (term287 A P s).
Proof. exact (EQ_MP (@lem4874712 A P s) (@lem4874711 A P s)). Qed.
Lemma lem4874746 {A : Type'} (P : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A (@ARBITRARY A) P s) = (term287 A P s).
Proof. exact (@lem4874745 A P s). Qed.
Lemma lem4874747 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term294 A P s t) = (term295 A P s t).
Proof. exact (@lem4874746 A P (@UNION A s t)). Qed.
Lemma lem4874748 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term296 A P s t) = (term297 A P s t).
Proof. exact (MK_COMB (@lem4874743 A s P t) (@lem4874747 A P s t)). Qed.
Lemma lem4874749 {A : Type'} (P : type686 A) (s : A -> Prop) : (term298 A P s) = (term299 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4874748 A P s t)). Qed.
Lemma lem4874750 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4874751 {A : Type'} (P : type686 A) (s : A -> Prop) : (term300 A P s) = (term301 A P s).
Proof. exact (MK_COMB (@lem4874750 A) (@lem4874749 A P s)). Qed.
Lemma lem4874752 {A : Type'} (P : type686 A) : (term302 A P) = (term303 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4874751 A P s)). Qed.
Lemma lem4874753 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4874754 {A : Type'} (P : type686 A) : (term304 A P) = (term305 A P).
Proof. exact (MK_COMB (@lem4874753 A) (@lem4874752 A P)). Qed.
Lemma lem4874755 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4874756 {A : Type'} (P : type686 A) : (term306 A P) = (term307 A P).
Proof. exact (MK_COMB (@lem4874755) (@lem4874754 A P)). Qed.
Lemma lem4874770 {A : Type'} (P : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A (@ARBITRARY A) P s) = (term287 A P s).
Proof. exact (EQ_MP (@lem4874712 A P s) (@lem4874711 A P s)). Qed.
Lemma lem4874771 {A : Type'} (P : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A (@ARBITRARY A) P s) = (term287 A P s).
Proof. exact (@lem4874770 A P s). Qed.
Lemma lem4874772 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term294 A P s t) = (term295 A P s t).
Proof. exact (@lem4874771 A P (@UNION A s t)). Qed.
Lemma lem4874773 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term308 A s P t) = (term308 A s P t).
Proof. exact (eq_refl (term308 A s P t)). Qed.
Lemma lem4874774 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term309 A P s t) = (term310 A P s t).
Proof. exact (MK_COMB (@lem4874773 A s P t) (@lem4874772 A P s t)). Qed.
Lemma lem4874775 {A : Type'} (P : type686 A) (s : A -> Prop) : (term311 A P s) = (term312 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4874774 A P s t)). Qed.
Lemma lem4874776 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4874777 {A : Type'} (P : type686 A) (s : A -> Prop) : (term313 A P s) = (term314 A P s).
Proof. exact (MK_COMB (@lem4874776 A) (@lem4874775 A P s)). Qed.
Lemma lem4874778 {A : Type'} (P : type686 A) : (term315 A P) = (term316 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4874777 A P s)). Qed.
Lemma lem4874779 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4874780 {A : Type'} (P : type686 A) : (term317 A P) = (term318 A P).
Proof. exact (MK_COMB (@lem4874779 A) (@lem4874778 A P)). Qed.
Lemma lem4874781 {A : Type'} (P : type686 A) : ((term304 A P) = (term317 A P)) = ((term305 A P) = (term318 A P)).
Proof. exact (MK_COMB (@lem4874756 A P) (@lem4874780 A P)). Qed.
Lemma lem4874782 {A : Type'} : (term319 A) = (term320 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4874781 A P)). Qed.
Lemma lem4874783 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4874784 {A : Type'} : (term321 A) = (term322 A).
Proof. exact (MK_COMB (@lem4874783 A) (@lem4874782 A)). Qed.
Lemma lem4874785 {A : Type'} : (term322 A) = (term321 A).
Proof. exact (SYM (@lem4874784 A)). Qed.
Lemma lem4874805 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) : (term229 _112027 s t) = (term230 _112027 s t).
Proof. exact (EQ_MP (@lem4874129 _112027 s t) (@lem4874706 _112027 s t)). Qed.
Lemma lem4874806 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term229 A s t) = (term230 A s t).
Proof. exact (@lem4874805 A s t). Qed.
Lemma lem4874807 {A : Type'} (P : type686 A) : (term323 A P) = (term323 A P).
Proof. exact (eq_refl (term323 A P)). Qed.
Lemma lem4874808 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term295 A P s t) = (term324 A P s t).
Proof. exact (MK_COMB (@lem4874807 A P) (@lem4874806 A s t)). Qed.
Lemma lem4874809 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term293 A s P t) = (term293 A s P t).
Proof. exact (eq_refl (term293 A s P t)). Qed.
Lemma lem4874810 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term297 A P s t) = (term325 A P s t).
Proof. exact (MK_COMB (@lem4874809 A s P t) (@lem4874808 A P s t)). Qed.
Lemma lem4874813 {A : Type'} (P : type686 A) (s : A -> Prop) : (term299 A P s) = (term326 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4874810 A P s t)). Qed.
Lemma lem4874814 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4874815 {A : Type'} (P : type686 A) (s : A -> Prop) : (term301 A P s) = (term327 A P s).
Proof. exact (MK_COMB (@lem4874814 A) (@lem4874813 A P s)). Qed.
Lemma lem4874820 {A : Type'} (P : type686 A) : (term303 A P) = (term328 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4874815 A P s)). Qed.
Lemma lem4874821 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4874822 {A : Type'} (P : type686 A) : (term305 A P) = (term329 A P).
Proof. exact (MK_COMB (@lem4874821 A) (@lem4874820 A P)). Qed.
Lemma lem4874827 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4874828 {A : Type'} (P : type686 A) : (term307 A P) = (term330 A P).
Proof. exact (MK_COMB (@lem4874827) (@lem4874822 A P)). Qed.
Lemma lem4874842 {_112027 : Type'} (s : _112027 -> Prop) (t : _112027 -> Prop) : (term229 _112027 s t) = (term230 _112027 s t).
Proof. exact (EQ_MP (@lem4874129 _112027 s t) (@lem4874706 _112027 s t)). Qed.
Lemma lem4874843 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term229 A s t) = (term230 A s t).
Proof. exact (@lem4874842 A s t). Qed.
Lemma lem4874844 {A : Type'} (P : type686 A) : (term323 A P) = (term323 A P).
Proof. exact (eq_refl (term323 A P)). Qed.
Lemma lem4874845 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term295 A P s t) = (term324 A P s t).
Proof. exact (MK_COMB (@lem4874844 A P) (@lem4874843 A s t)). Qed.
Lemma lem4874846 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term308 A s P t) = (term308 A s P t).
Proof. exact (eq_refl (term308 A s P t)). Qed.
Lemma lem4874847 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term310 A P s t) = (term331 A P s t).
Proof. exact (MK_COMB (@lem4874846 A s P t) (@lem4874845 A P s t)). Qed.
Lemma lem4874850 {A : Type'} (P : type686 A) (s : A -> Prop) : (term312 A P s) = (term332 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4874847 A P s t)). Qed.
Lemma lem4874851 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4874852 {A : Type'} (P : type686 A) (s : A -> Prop) : (term314 A P s) = (term333 A P s).
Proof. exact (MK_COMB (@lem4874851 A) (@lem4874850 A P s)). Qed.
Lemma lem4874857 {A : Type'} (P : type686 A) : (term316 A P) = (term334 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4874852 A P s)). Qed.
Lemma lem4874858 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4874859 {A : Type'} (P : type686 A) : (term318 A P) = (term335 A P).
Proof. exact (MK_COMB (@lem4874858 A) (@lem4874857 A P)). Qed.
Lemma lem4874864 {A : Type'} (P : type686 A) : ((term305 A P) = (term318 A P)) = ((term329 A P) = (term335 A P)).
Proof. exact (MK_COMB (@lem4874828 A P) (@lem4874859 A P)). Qed.
Lemma lem4874867 {A : Type'} : (term320 A) = (term336 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4874864 A P)). Qed.
Lemma lem4874868 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4874869 {A : Type'} : (term322 A) = (term337 A).
Proof. exact (MK_COMB (@lem4874868 A) (@lem4874867 A)). Qed.
Lemma lem4874874 {A : Type'} : (term337 A) = (term322 A).
Proof. exact (SYM (@lem4874869 A)). Qed.
Lemma lem4874902 {_112000 : Type'} (P : type686 _112000) : (term3 _112000 P) = (term4 _112000 P).
Proof. exact (EQ_MP (@lem4873449 _112000 P) (@lem4874103 _112000 P)). Qed.
Lemma lem4874903 {A : Type'} (P : type686 A) : (term3 A P) = (term4 A P).
Proof. exact (@lem4874902 A P). Qed.
Lemma lem4874904 {A : Type'} (P : type686 A) : (term338 A P) = (term339 A P).
Proof. exact (@lem4874903 A (term340 A P)). Qed.
Lemma lem4874905 {A : Type'} (P : type686 A) (s : A -> Prop) : (term341 A P s) = (term327 A P s).
Proof. exact (eq_refl (term341 A P s)). Qed.
Lemma lem4874906 {A : Type'} (P : type686 A) : (term342 A P) = (term328 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4874905 A P s)). Qed.
Lemma lem4874907 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4874908 {A : Type'} (P : type686 A) : (term338 A P) = (term329 A P).
Proof. exact (MK_COMB (@lem4874907 A) (@lem4874906 A P)). Qed.
Lemma lem4874909 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4874910 {A : Type'} (P : type686 A) : (term343 A P) = (term330 A P).
Proof. exact (MK_COMB (@lem4874909) (@lem4874908 A P)). Qed.
Lemma lem4874911 {A : Type'} (P : type686 A) (s : A -> Prop) : (term344 A P s) = (term345 A P s).
Proof. exact (eq_refl (term344 A P s)). Qed.
Lemma lem4874912 {A : Type'} (P : type686 A) : (term346 A P) = (term340 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4874911 A P s)). Qed.
Lemma lem4874913 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4874914 {A : Type'} (P : type686 A) : (term339 A P) = (term347 A P).
Proof. exact (MK_COMB (@lem4874913 A) (@lem4874912 A P)). Qed.
Lemma lem4874915 {A : Type'} (P : type686 A) : ((term338 A P) = (term339 A P)) = ((term329 A P) = (term347 A P)).
Proof. exact (MK_COMB (@lem4874910 A P) (@lem4874914 A P)). Qed.
Lemma lem4874916 {A : Type'} (P : type686 A) : (term329 A P) = (term347 A P).
Proof. exact (EQ_MP (@lem4874915 A P) (@lem4874904 A P)). Qed.
Lemma lem4874942 {_112000 : Type'} (P : type686 _112000) : (term3 _112000 P) = (term4 _112000 P).
Proof. exact (EQ_MP (@lem4873449 _112000 P) (@lem4874103 _112000 P)). Qed.
Lemma lem4874943 {A : Type'} (P : type686 A) : (term3 A P) = (term4 A P).
Proof. exact (@lem4874942 A P). Qed.
Lemma lem4874944 {A : Type'} (P : type686 A) (s : A -> Prop) : (term348 A P s) = (term349 A P s).
Proof. exact (@lem4874943 A (term350 A P s)). Qed.
Lemma lem4874945 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term351 A P s t) = (term352 A P s t).
Proof. exact (eq_refl (term351 A P s t)). Qed.
Lemma lem4874946 {A : Type'} (P : type686 A) (s : A -> Prop) : (term353 A P s) = (term354 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4874945 A P s t)). Qed.
Lemma lem4874947 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4874948 {A : Type'} (P : type686 A) (s : A -> Prop) : (term348 A P s) = (term345 A P s).
Proof. exact (MK_COMB (@lem4874947 A) (@lem4874946 A P s)). Qed.
Lemma lem4874949 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4874950 {A : Type'} (P : type686 A) (s : A -> Prop) : (term355 A P s) = (term356 A P s).
Proof. exact (MK_COMB (@lem4874949) (@lem4874948 A P s)). Qed.
Lemma lem4874951 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term357 A P s t) = (term358 A P s t).
Proof. exact (eq_refl (term357 A P s t)). Qed.
Lemma lem4874952 {A : Type'} (P : type686 A) (s : A -> Prop) : (term359 A P s) = (term350 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4874951 A P s t)). Qed.
Lemma lem4874953 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4874954 {A : Type'} (P : type686 A) (s : A -> Prop) : (term349 A P s) = (term360 A P s).
Proof. exact (MK_COMB (@lem4874953 A) (@lem4874952 A P s)). Qed.
Lemma lem4874955 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term348 A P s) = (term349 A P s)) = ((term345 A P s) = (term360 A P s)).
Proof. exact (MK_COMB (@lem4874950 A P s) (@lem4874954 A P s)). Qed.
Lemma lem4874956 {A : Type'} (P : type686 A) (s : A -> Prop) : (term345 A P s) = (term360 A P s).
Proof. exact (EQ_MP (@lem4874955 A P s) (@lem4874944 A P s)). Qed.
Lemma lem4874981 {A : Type'} (P : type686 A) : (term340 A P) = (term361 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4874956 A P s)). Qed.
Lemma lem4874982 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4874983 {A : Type'} (P : type686 A) : (term347 A P) = (term362 A P).
Proof. exact (MK_COMB (@lem4874982 A) (@lem4874981 A P)). Qed.
Lemma lem4875004 {A : Type'} (P : type686 A) : (term329 A P) = (term362 A P).
Proof. exact (TRANS (@lem4874916 A P) (@lem4874983 A P)). Qed.
Lemma lem4875005 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4875006 {A : Type'} (P : type686 A) : (term330 A P) = (term363 A P).
Proof. exact (MK_COMB (@lem4875005) (@lem4875004 A P)). Qed.
Lemma lem4875051 {A : Type'} (P : type686 A) : (term335 A P) = (term335 A P).
Proof. exact (eq_refl (term335 A P)). Qed.
Lemma lem4875052 {A : Type'} (P : type686 A) : ((term329 A P) = (term335 A P)) = ((term362 A P) = (term335 A P)).
Proof. exact (MK_COMB (@lem4875006 A P) (@lem4875051 A P)). Qed.
Lemma lem4875055 {A : Type'} : (term336 A) = (term364 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4875052 A P)). Qed.
Lemma lem4875056 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4875057 {A : Type'} : (term337 A) = (term365 A).
Proof. exact (MK_COMB (@lem4875056 A) (@lem4875055 A)). Qed.
Lemma lem4875078 {A : Type'} : (term365 A) = (term337 A).
Proof. exact (SYM (@lem4875057 A)). Qed.
Lemma lem4875086 {A : Type'} (P : type686 A) : (term227 A P) = (term228 A P).
Proof. exact (EQ_MP (@lem4873434 A P) (@lem4873433 A P)). Qed.
Lemma lem4875087 {A : Type'} (P : type686 A) : (term227 A P) = (term228 A P).
Proof. exact (@lem4875086 A P). Qed.
Lemma lem4875088 {A : Type'} (P : type686 A) : (term362 A P) = (term366 A P).
Proof. exact (@lem4875087 A (term23 A P)). Qed.
Lemma lem4875102 {A B : Type'} (f : A -> B) (y : A) : (term367 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4875103 {A : Type'} (f : type686 A) (y : A -> Prop) : (term37 A f y) = (f y).
Proof. exact (@lem4875102 (A -> Prop) Prop f y). Qed.
Lemma lem4875104 {A : Type'} (P : type686 A) (s : A -> Prop) : (term368 A P s) = (term29 A P s).
Proof. exact (@lem4875103 A (term23 A P) s). Qed.
Lemma lem4875105 {A : Type'} (P : type686 A) (s : A -> Prop) : (term29 A P s) = (term22 A P s).
Proof. exact (eq_refl (term29 A P s)). Qed.
Lemma lem4875106 {A : Type'} (P : type686 A) : (term369 A P) = (term23 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4875105 A P s)). Qed.
Lemma lem4875107 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4875108 {A : Type'} (P : type686 A) (s : A -> Prop) : (term368 A P s) = (term29 A P s).
Proof. exact (MK_COMB (@lem4875106 A P) (@lem4875107 A s)). Qed.
Lemma lem4875109 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4875110 {A : Type'} (P : type686 A) (s : A -> Prop) : (term370 A P s) = (term371 A P s).
Proof. exact (MK_COMB (@lem4875109) (@lem4875108 A P s)). Qed.
Lemma lem4875111 {A : Type'} (P : type686 A) (s : A -> Prop) : (term29 A P s) = (term22 A P s).
Proof. exact (eq_refl (term29 A P s)). Qed.
Lemma lem4875112 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term368 A P s) = (term29 A P s)) = ((term29 A P s) = (term22 A P s)).
Proof. exact (MK_COMB (@lem4875110 A P s) (@lem4875111 A P s)). Qed.
Lemma lem4875113 {A : Type'} (P : type686 A) (s : A -> Prop) : (term29 A P s) = (term22 A P s).
Proof. exact (EQ_MP (@lem4875112 A P s) (@lem4875104 A P s)). Qed.
Lemma lem4875114 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4875115 {A : Type'} (P : type686 A) (s : A -> Prop) : (term372 A P s) = (term373 A P s).
Proof. exact (MK_COMB (@lem4875114) (@lem4875113 A P s)). Qed.
Lemma lem4875117 {A B : Type'} (f : A -> B) (y : A) : (term367 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4875118 {A : Type'} (f : type686 A) (y : A -> Prop) : (term37 A f y) = (f y).
Proof. exact (@lem4875117 (A -> Prop) Prop f y). Qed.
Lemma lem4875119 {A : Type'} (P : type686 A) (t : A -> Prop) : (term368 A P t) = (term29 A P t).
Proof. exact (@lem4875118 A (term23 A P) t). Qed.
Lemma lem4875120 {A : Type'} (P : type686 A) (s : A -> Prop) : (term29 A P s) = (term22 A P s).
Proof. exact (eq_refl (term29 A P s)). Qed.
Lemma lem4875121 {A : Type'} (P : type686 A) : (term369 A P) = (term23 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4875120 A P s)). Qed.
Lemma lem4875122 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4875123 {A : Type'} (P : type686 A) (t : A -> Prop) : (term368 A P t) = (term29 A P t).
Proof. exact (MK_COMB (@lem4875121 A P) (@lem4875122 A t)). Qed.
Lemma lem4875124 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4875125 {A : Type'} (P : type686 A) (t : A -> Prop) : (term370 A P t) = (term371 A P t).
Proof. exact (MK_COMB (@lem4875124) (@lem4875123 A P t)). Qed.
Lemma lem4875126 {A : Type'} (P : type686 A) (t : A -> Prop) : (term29 A P t) = (term22 A P t).
Proof. exact (eq_refl (term29 A P t)). Qed.
Lemma lem4875127 {A : Type'} (P : type686 A) (t : A -> Prop) : ((term368 A P t) = (term29 A P t)) = ((term29 A P t) = (term22 A P t)).
Proof. exact (MK_COMB (@lem4875125 A P t) (@lem4875126 A P t)). Qed.
Lemma lem4875128 {A : Type'} (P : type686 A) (t : A -> Prop) : (term29 A P t) = (term22 A P t).
Proof. exact (EQ_MP (@lem4875127 A P t) (@lem4875119 A P t)). Qed.
Lemma lem4875129 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term374 A s P t) = (term375 A s P t).
Proof. exact (MK_COMB (@lem4875115 A P s) (@lem4875128 A P t)). Qed.
Lemma lem4875132 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4875133 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term376 A s P t) = (term377 A s P t).
Proof. exact (MK_COMB (@lem4875132) (@lem4875129 A s P t)). Qed.
Lemma lem4875134 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term378 A P s t) = (term378 A P s t).
Proof. exact (eq_refl (term378 A P s t)). Qed.
Lemma lem4875135 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term379 A P s t) = (term380 A P s t).
Proof. exact (MK_COMB (@lem4875133 A s P t) (@lem4875134 A P s t)). Qed.
Lemma lem4875138 {A : Type'} (P : type686 A) (s : A -> Prop) : (term381 A P s) = (term382 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4875135 A P s t)). Qed.
Lemma lem4875139 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4875140 {A : Type'} (P : type686 A) (s : A -> Prop) : (term383 A P s) = (term384 A P s).
Proof. exact (MK_COMB (@lem4875139 A) (@lem4875138 A P s)). Qed.
Lemma lem4875145 {A : Type'} (P : type686 A) : (term385 A P) = (term386 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4875140 A P s)). Qed.
Lemma lem4875146 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4875147 {A : Type'} (P : type686 A) : (term366 A P) = (term387 A P).
Proof. exact (MK_COMB (@lem4875146 A) (@lem4875145 A P)). Qed.
Lemma lem4875152 {A : Type'} (P : type686 A) : (term362 A P) = (term387 A P).
Proof. exact (TRANS (@lem4875088 A P) (@lem4875147 A P)). Qed.
Lemma lem4875153 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4875154 {A : Type'} (P : type686 A) : (term363 A P) = (term388 A P).
Proof. exact (MK_COMB (@lem4875153) (@lem4875152 A P)). Qed.
Lemma lem4875167 {A : Type'} (P : type686 A) : (term335 A P) = (term335 A P).
Proof. exact (eq_refl (term335 A P)). Qed.
Lemma lem4875168 {A : Type'} (P : type686 A) : ((term362 A P) = (term335 A P)) = ((term387 A P) = (term335 A P)).
Proof. exact (MK_COMB (@lem4875154 A P) (@lem4875167 A P)). Qed.
Lemma lem4875171 {A : Type'} : (term364 A) = (term389 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4875168 A P)). Qed.
Lemma lem4875172 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4875173 {A : Type'} : (term365 A) = (term390 A).
Proof. exact (MK_COMB (@lem4875172 A) (@lem4875171 A)). Qed.
Lemma lem4875178 {A : Type'} : (term390 A) = (term365 A).
Proof. exact (SYM (@lem4875173 A)). Qed.
Lemma lem4875198 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) : (@INTER _111988 s t) = (term157 _111988 s t).
Proof. exact (EQ_MP (@lem4872854 _111988 s t) (@lem4873431 _111988 s t)). Qed.
Lemma lem4875199 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@INTER A s t) = (term157 A s t).
Proof. exact (@lem4875198 A s t). Qed.
Lemma lem4875200 {A : Type'} (P : type686 A) : (term323 A P) = (term323 A P).
Proof. exact (eq_refl (term323 A P)). Qed.
Lemma lem4875201 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term378 A P s t) = (term391 A P s t).
Proof. exact (MK_COMB (@lem4875200 A P) (@lem4875199 A s t)). Qed.
Lemma lem4875202 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term377 A s P t) = (term377 A s P t).
Proof. exact (eq_refl (term377 A s P t)). Qed.
Lemma lem4875203 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term380 A P s t) = (term392 A P s t).
Proof. exact (MK_COMB (@lem4875202 A s P t) (@lem4875201 A P s t)). Qed.
Lemma lem4875206 {A : Type'} (P : type686 A) (s : A -> Prop) : (term382 A P s) = (term393 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4875203 A P s t)). Qed.
Lemma lem4875207 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4875208 {A : Type'} (P : type686 A) (s : A -> Prop) : (term384 A P s) = (term394 A P s).
Proof. exact (MK_COMB (@lem4875207 A) (@lem4875206 A P s)). Qed.
Lemma lem4875213 {A : Type'} (P : type686 A) : (term386 A P) = (term395 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4875208 A P s)). Qed.
Lemma lem4875214 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4875215 {A : Type'} (P : type686 A) : (term387 A P) = (term396 A P).
Proof. exact (MK_COMB (@lem4875214 A) (@lem4875213 A P)). Qed.
Lemma lem4875220 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4875221 {A : Type'} (P : type686 A) : (term388 A P) = (term397 A P).
Proof. exact (MK_COMB (@lem4875220) (@lem4875215 A P)). Qed.
Lemma lem4875235 {_111988 : Type'} (s : _111988 -> Prop) (t : _111988 -> Prop) : (@INTER _111988 s t) = (term157 _111988 s t).
Proof. exact (EQ_MP (@lem4872854 _111988 s t) (@lem4873431 _111988 s t)). Qed.
Lemma lem4875236 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@INTER A s t) = (term157 A s t).
Proof. exact (@lem4875235 A s t). Qed.
Lemma lem4875237 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term230 A s t) = (term398 A s t).
Proof. exact (@lem4875236 A (@DIFF A (@UNIV A) s) (@DIFF A (@UNIV A) t)). Qed.
Lemma lem4875238 {A : Type'} (P : type686 A) : (term323 A P) = (term323 A P).
Proof. exact (eq_refl (term323 A P)). Qed.
Lemma lem4875239 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term324 A P s t) = (term399 A P s t).
Proof. exact (MK_COMB (@lem4875238 A P) (@lem4875237 A s t)). Qed.
Lemma lem4875240 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term308 A s P t) = (term308 A s P t).
Proof. exact (eq_refl (term308 A s P t)). Qed.
Lemma lem4875241 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term331 A P s t) = (term400 A P s t).
Proof. exact (MK_COMB (@lem4875240 A s P t) (@lem4875239 A P s t)). Qed.
Lemma lem4875244 {A : Type'} (P : type686 A) (s : A -> Prop) : (term332 A P s) = (term401 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4875241 A P s t)). Qed.
Lemma lem4875245 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4875246 {A : Type'} (P : type686 A) (s : A -> Prop) : (term333 A P s) = (term402 A P s).
Proof. exact (MK_COMB (@lem4875245 A) (@lem4875244 A P s)). Qed.
Lemma lem4875251 {A : Type'} (P : type686 A) : (term334 A P) = (term403 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4875246 A P s)). Qed.
Lemma lem4875252 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4875253 {A : Type'} (P : type686 A) : (term335 A P) = (term404 A P).
Proof. exact (MK_COMB (@lem4875252 A) (@lem4875251 A P)). Qed.
Lemma lem4875258 {A : Type'} (P : type686 A) : ((term387 A P) = (term335 A P)) = ((term396 A P) = (term404 A P)).
Proof. exact (MK_COMB (@lem4875221 A P) (@lem4875253 A P)). Qed.
Lemma lem4875261 {A : Type'} : (term389 A) = (term405 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4875258 A P)). Qed.
Lemma lem4875262 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4875263 {A : Type'} : (term390 A) = (term406 A).
Proof. exact (MK_COMB (@lem4875262 A) (@lem4875261 A)). Qed.
Lemma lem4875268 {A : Type'} : (term406 A) = (term390 A).
Proof. exact (SYM (@lem4875263 A)). Qed.
Lemma lem4875296 {_111961 : Type'} (P : type686 _111961) : (term3 _111961 P) = (term4 _111961 P).
Proof. exact (EQ_MP (@lem4872174 _111961 P) (@lem4872828 _111961 P)). Qed.
Lemma lem4875297 {A : Type'} (P : type686 A) : (term3 A P) = (term4 A P).
Proof. exact (@lem4875296 A P). Qed.
Lemma lem4875298 {A : Type'} (P : type686 A) : (term407 A P) = (term408 A P).
Proof. exact (@lem4875297 A (term409 A P)). Qed.
Lemma lem4875299 {A : Type'} (P : type686 A) (s : A -> Prop) : (term410 A P s) = (term394 A P s).
Proof. exact (eq_refl (term410 A P s)). Qed.
Lemma lem4875300 {A : Type'} (P : type686 A) : (term411 A P) = (term395 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4875299 A P s)). Qed.
Lemma lem4875301 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4875302 {A : Type'} (P : type686 A) : (term407 A P) = (term396 A P).
Proof. exact (MK_COMB (@lem4875301 A) (@lem4875300 A P)). Qed.
Lemma lem4875303 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4875304 {A : Type'} (P : type686 A) : (term412 A P) = (term397 A P).
Proof. exact (MK_COMB (@lem4875303) (@lem4875302 A P)). Qed.
Lemma lem4875305 {A : Type'} (P : type686 A) (s : A -> Prop) : (term413 A P s) = (term414 A P s).
Proof. exact (eq_refl (term413 A P s)). Qed.
Lemma lem4875306 {A : Type'} (P : type686 A) : (term415 A P) = (term409 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4875305 A P s)). Qed.
Lemma lem4875307 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4875308 {A : Type'} (P : type686 A) : (term408 A P) = (term416 A P).
Proof. exact (MK_COMB (@lem4875307 A) (@lem4875306 A P)). Qed.
Lemma lem4875309 {A : Type'} (P : type686 A) : ((term407 A P) = (term408 A P)) = ((term396 A P) = (term416 A P)).
Proof. exact (MK_COMB (@lem4875304 A P) (@lem4875308 A P)). Qed.
Lemma lem4875310 {A : Type'} (P : type686 A) : (term396 A P) = (term416 A P).
Proof. exact (EQ_MP (@lem4875309 A P) (@lem4875298 A P)). Qed.
Lemma lem4875336 {_111961 : Type'} (P : type686 _111961) : (term3 _111961 P) = (term4 _111961 P).
Proof. exact (EQ_MP (@lem4872174 _111961 P) (@lem4872828 _111961 P)). Qed.
Lemma lem4875337 {A : Type'} (P : type686 A) : (term3 A P) = (term4 A P).
Proof. exact (@lem4875336 A P). Qed.
Lemma lem4875338 {A : Type'} (P : type686 A) (s : A -> Prop) : (term417 A P s) = (term418 A P s).
Proof. exact (@lem4875337 A (term312 A P s)). Qed.
Lemma lem4875339 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term419 A P s t) = (term420 A P s t).
Proof. exact (eq_refl (term419 A P s t)). Qed.
Lemma lem4875340 {A : Type'} (P : type686 A) (s : A -> Prop) : (term421 A P s) = (term422 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4875339 A P s t)). Qed.
Lemma lem4875341 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4875342 {A : Type'} (P : type686 A) (s : A -> Prop) : (term417 A P s) = (term414 A P s).
Proof. exact (MK_COMB (@lem4875341 A) (@lem4875340 A P s)). Qed.
Lemma lem4875343 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4875344 {A : Type'} (P : type686 A) (s : A -> Prop) : (term423 A P s) = (term424 A P s).
Proof. exact (MK_COMB (@lem4875343) (@lem4875342 A P s)). Qed.
Lemma lem4875345 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term425 A P s t) = (term310 A P s t).
Proof. exact (eq_refl (term425 A P s t)). Qed.
Lemma lem4875346 {A : Type'} (P : type686 A) (s : A -> Prop) : (term426 A P s) = (term312 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4875345 A P s t)). Qed.
Lemma lem4875347 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4875348 {A : Type'} (P : type686 A) (s : A -> Prop) : (term418 A P s) = (term314 A P s).
Proof. exact (MK_COMB (@lem4875347 A) (@lem4875346 A P s)). Qed.
Lemma lem4875349 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term417 A P s) = (term418 A P s)) = ((term414 A P s) = (term314 A P s)).
Proof. exact (MK_COMB (@lem4875344 A P s) (@lem4875348 A P s)). Qed.
Lemma lem4875350 {A : Type'} (P : type686 A) (s : A -> Prop) : (term414 A P s) = (term314 A P s).
Proof. exact (EQ_MP (@lem4875349 A P s) (@lem4875338 A P s)). Qed.
Lemma lem4875375 {A : Type'} (P : type686 A) : (term409 A P) = (term316 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4875350 A P s)). Qed.
Lemma lem4875376 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4875377 {A : Type'} (P : type686 A) : (term416 A P) = (term318 A P).
Proof. exact (MK_COMB (@lem4875376 A) (@lem4875375 A P)). Qed.
Lemma lem4875398 {A : Type'} (P : type686 A) : (term396 A P) = (term318 A P).
Proof. exact (TRANS (@lem4875310 A P) (@lem4875377 A P)). Qed.
Lemma lem4875399 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4875400 {A : Type'} (P : type686 A) : (term397 A P) = (term427 A P).
Proof. exact (MK_COMB (@lem4875399) (@lem4875398 A P)). Qed.
Lemma lem4875445 {A : Type'} (P : type686 A) : (term404 A P) = (term404 A P).
Proof. exact (eq_refl (term404 A P)). Qed.
Lemma lem4875446 {A : Type'} (P : type686 A) : ((term396 A P) = (term404 A P)) = ((term318 A P) = (term404 A P)).
Proof. exact (MK_COMB (@lem4875400 A P) (@lem4875445 A P)). Qed.
Lemma lem4875449 {A : Type'} : (term405 A) = (term428 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4875446 A P)). Qed.
Lemma lem4875450 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4875451 {A : Type'} : (term406 A) = (term429 A).
Proof. exact (MK_COMB (@lem4875450 A) (@lem4875449 A)). Qed.
Lemma lem4875472 {A : Type'} : (term429 A) = (term406 A).
Proof. exact (SYM (@lem4875451 A)). Qed.
Lemma lem4875504 {A : Type'} (s : A -> Prop) : (term1 A s) = s.
Proof. exact (EQ_MP (@lem4872159 A s) (@lem4872158 A s)). Qed.
Lemma lem4875505 {A : Type'} (s : A -> Prop) : (term1 A s) = s.
Proof. exact (@lem4875504 A s). Qed.
Lemma lem4875506 {A : Type'} : (@UNION A) = (@UNION A).
Proof. exact (eq_refl (@UNION A)). Qed.
Lemma lem4875507 {A : Type'} (s : A -> Prop) : (term430 A s) = (@UNION A s).
Proof. exact (MK_COMB (@lem4875506 A) (@lem4875505 A s)). Qed.
Lemma lem4875509 {A : Type'} (s : A -> Prop) : (term1 A s) = s.
Proof. exact (EQ_MP (@lem4872159 A s) (@lem4872158 A s)). Qed.
Lemma lem4875510 {A : Type'} (s : A -> Prop) : (term1 A s) = s.
Proof. exact (@lem4875509 A s). Qed.
Lemma lem4875511 {A : Type'} (t : A -> Prop) : (term1 A t) = t.
Proof. exact (@lem4875510 A t). Qed.
Lemma lem4875512 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term431 A s t) = (@UNION A s t).
Proof. exact (MK_COMB (@lem4875507 A s) (@lem4875511 A t)). Qed.
Lemma lem4875513 {A : Type'} : (@DIFF A (@UNIV A)) = (@DIFF A (@UNIV A)).
Proof. exact (eq_refl (@DIFF A (@UNIV A))). Qed.
Lemma lem4875514 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term398 A s t) = (term229 A s t).
Proof. exact (MK_COMB (@lem4875513 A) (@lem4875512 A s t)). Qed.
Lemma lem4875515 {A : Type'} (P : type686 A) : (term323 A P) = (term323 A P).
Proof. exact (eq_refl (term323 A P)). Qed.
Lemma lem4875516 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term399 A P s t) = (term295 A P s t).
Proof. exact (MK_COMB (@lem4875515 A P) (@lem4875514 A s t)). Qed.
Lemma lem4875517 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term308 A s P t) = (term308 A s P t).
Proof. exact (eq_refl (term308 A s P t)). Qed.
Lemma lem4875518 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term400 A P s t) = (term310 A P s t).
Proof. exact (MK_COMB (@lem4875517 A s P t) (@lem4875516 A P s t)). Qed.
Lemma lem4875521 {A : Type'} (P : type686 A) (s : A -> Prop) : (term401 A P s) = (term312 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4875518 A P s t)). Qed.
Lemma lem4875522 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4875523 {A : Type'} (P : type686 A) (s : A -> Prop) : (term402 A P s) = (term314 A P s).
Proof. exact (MK_COMB (@lem4875522 A) (@lem4875521 A P s)). Qed.
Lemma lem4875528 {A : Type'} (P : type686 A) : (term403 A P) = (term316 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4875523 A P s)). Qed.
Lemma lem4875529 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4875530 {A : Type'} (P : type686 A) : (term404 A P) = (term318 A P).
Proof. exact (MK_COMB (@lem4875529 A) (@lem4875528 A P)). Qed.
Lemma lem4875535 {A : Type'} (P : type686 A) : (term427 A P) = (term427 A P).
Proof. exact (eq_refl (term427 A P)). Qed.
Lemma lem4875536 {A : Type'} (P : type686 A) : ((term318 A P) = (term404 A P)) = ((term318 A P) = (term318 A P)).
Proof. exact (MK_COMB (@lem4875535 A P) (@lem4875530 A P)). Qed.
Lemma lem4875538 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4875539 (x : Prop) : (x = x) = True.
Proof. exact (@lem4875538 Prop x). Qed.
Lemma lem4875540 {A : Type'} (P : type686 A) : ((term318 A P) = (term318 A P)) = True.
Proof. exact (@lem4875539 (term318 A P)). Qed.
Lemma lem4875541 {A : Type'} (P : type686 A) : ((term318 A P) = (term404 A P)) = True.
Proof. exact (TRANS (@lem4875536 A P) (@lem4875540 A P)). Qed.
Lemma lem4875542 {A : Type'} : (term428 A) = (term432 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4875541 A P)). Qed.
Lemma lem4875543 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4875544 {A : Type'} : (term429 A) = (term433 A).
Proof. exact (MK_COMB (@lem4875543 A) (@lem4875542 A)). Qed.
Lemma lem4875546 {A : Type'} (t : Prop) : (term434 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4875547 {A : Type'} (t : Prop) : (term435 A t) = t.
Proof. exact (@lem4875546 (type686 A) t). Qed.
Lemma lem4875548 {A : Type'} : (term433 A) = True.
Proof. exact (@lem4875547 A True). Qed.
Lemma lem4875549 {A : Type'} : (term429 A) = True.
Proof. exact (TRANS (@lem4875544 A) (@lem4875548 A)). Qed.
Lemma lem4875550 {A : Type'} : True = (term429 A).
Proof. exact (SYM (@lem4875549 A)). Qed.
Lemma lem4875551 {A : Type'} : term429 A.
Proof. exact (EQ_MP (@lem4875550 A) (@lem0)). Qed.
Lemma lem4875552 {A : Type'} : term406 A.
Proof. exact (EQ_MP (@lem4875472 A) (@lem4875551 A)). Qed.
Lemma lem4875553 {A : Type'} : term390 A.
Proof. exact (EQ_MP (@lem4875268 A) (@lem4875552 A)). Qed.
Lemma lem4875554 {A : Type'} : term365 A.
Proof. exact (EQ_MP (@lem4875178 A) (@lem4875553 A)). Qed.
Lemma lem4875555 {A : Type'} : term337 A.
Proof. exact (EQ_MP (@lem4875078 A) (@lem4875554 A)). Qed.
Lemma lem4875556 {A : Type'} : term322 A.
Proof. exact (EQ_MP (@lem4874874 A) (@lem4875555 A)). Qed.
Lemma lem4875557 {A : Type'} : term321 A.
Proof. exact (EQ_MP (@lem4874785 A) (@lem4875556 A)). Qed.
