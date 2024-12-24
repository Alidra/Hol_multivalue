Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARBITRARY_UNION_OF_INTER_EQ_term_abbrevs.
Require Import ARBITRARY_UNION_OF_INC_spec.
Require Import ARBITRARY_UNION_OF_UNIONS_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FORALL_IN_IMAGE_spec.
Require Import INTER_UNIONS_spec.
Require Import SIMPLE_IMAGE_spec.
Require Import UNION_OF_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
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
Require Import thm32_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem4869077 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem4869078 {A : Type'} (P : type686 A) (h1 : term0 A) : term1 A P.
Proof. exact (@lem4869077 A h1 P). Qed.
Lemma lem4869079 {A : Type'} (P : type686 A) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem4869080 {A : Type'} (P : type686 A) (h1 : term0 A) : term2 A P.
Proof. exact (EQ_MP (@lem4869079 A P) (@lem4869078 A P h1)). Qed.
Lemma lem4869081 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term0 A) : term3 A P u.
Proof. exact (@lem4869080 A P h1 u). Qed.
Lemma lem4869082 {A : Type'} (P : type686 A) (u : type686 A) : (term3 A P u) = (term4 A P u).
Proof. exact (eq_refl (term3 A P u)). Qed.
Lemma lem4869083 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term0 A) : term4 A P u.
Proof. exact (EQ_MP (@lem4869082 A P u) (@lem4869081 A P u h1)). Qed.
Lemma lem4869084 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term5 A u P) : term5 A u P.
Proof. exact (h1). Qed.
Lemma lem4869085 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term5 A u P) (h2 : term0 A) : term6 A P u.
Proof. exact (@lem4869083 A P u h2 (@lem4869084 A u P h1)). Qed.
Lemma lem4869086 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term5 A u P) : term7 A P u.
Proof. exact (fun h0 : term0 A => @lem4869085 A u P h1 h0). Qed.
Lemma lem4869087 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem4869088 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term5 A u P) (h2 : term0 A) : term6 A P u.
Proof. exact (@lem4869086 A u P h1 (@lem4869087 A h2)). Qed.
Lemma lem4869089 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term0 A) : term4 A P u.
Proof. exact (fun h0 : term5 A u P => @lem4869088 A u P h0 h1). Qed.
Lemma lem4869090 {A : Type'} (P : type686 A) (h1 : term0 A) : term2 A P.
Proof. exact (fun u : type686 A => @lem4869089 A P u h1). Qed.
Lemma lem4869091 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (fun P : type686 A => @lem4869090 A P h1). Qed.
Lemma lem4869092 {A : Type'} : term8 A.
Proof. exact (fun h0 : term0 A => @lem4869091 A h0). Qed.
Lemma lem4869093 {A : Type'} : term0 A.
Proof. exact (@lem4869092 A (@lem4868514 A)). Qed.
Lemma lem4869094 {A : Type'} (P : type686 A) : term1 A P.
Proof. exact (@lem4869093 A P). Qed.
Lemma lem4869095 {A : Type'} (P : type686 A) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem4869096 {A : Type'} (P : type686 A) : term2 A P.
Proof. exact (EQ_MP (@lem4869095 A P) (@lem4869094 A P)). Qed.
Lemma lem4869097 {A : Type'} (P : type686 A) (u : type686 A) : term3 A P u.
Proof. exact (@lem4869096 A P u). Qed.
Lemma lem4869098 {A : Type'} (P : type686 A) (u : type686 A) : (term3 A P u) = (term4 A P u).
Proof. exact (eq_refl (term3 A P u)). Qed.
Lemma lem4869100 {A : Type'} (P : type180 A) : term9 A P.
Proof. exact (@lem4841086 A P). Qed.
Lemma lem4869101 {A : Type'} (P : type180 A) : (term9 A P) = (term10 A P).
Proof. exact (eq_refl (term9 A P)). Qed.
Lemma lem4869102 {A : Type'} (P : type180 A) : term10 A P.
Proof. exact (EQ_MP (@lem4869101 A P) (@lem4869100 A P)). Qed.
Lemma lem4869103 {A : Type'} (P : type180 A) (Q : type686 A) : term11 A P Q.
Proof. exact (@lem4869102 A P Q). Qed.
Lemma lem4869104 {A : Type'} (P : type180 A) (Q : type686 A) : (term11 A P Q) = ((@UNION_OF A P Q) = (term12 A P Q)).
Proof. exact (eq_refl (term11 A P Q)). Qed.
Lemma lem4869106 (t1 : Prop) : term13 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4869107 (t1 : Prop) : (term13 t1) = (term14 t1).
Proof. exact (eq_refl (term13 t1)). Qed.
Lemma lem4869108 (t1 : Prop) : term14 t1.
Proof. exact (EQ_MP (@lem4869107 t1) (@lem4869106 t1)). Qed.
Lemma lem4869109 (t1 : Prop) (t2 : Prop) : term15 t1 t2.
Proof. exact (@lem4869108 t1 t2). Qed.
Lemma lem4869110 (t1 : Prop) (t2 : Prop) : (term15 t1 t2) = (term16 t1 t2).
Proof. exact (eq_refl (term15 t1 t2)). Qed.
Lemma lem4869111 (t1 : Prop) (t2 : Prop) : term16 t1 t2.
Proof. exact (EQ_MP (@lem4869110 t1 t2) (@lem4869109 t1 t2)). Qed.
Lemma lem4869112 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term17 t1 t2 t3.
Proof. exact (@lem4869111 t1 t2 t3). Qed.
Lemma lem4869113 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term17 t1 t2 t3) = ((term18 t1 t2 t3) = (term19 t1 t2 t3)).
Proof. exact (eq_refl (term17 t1 t2 t3)). Qed.
Lemma lem4869114 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term18 t1 t2 t3) = (term19 t1 t2 t3).
Proof. exact (EQ_MP (@lem4869113 t1 t2 t3) (@lem4869112 t1 t2 t3)). Qed.
Lemma lem4869115 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term19 t1 t2 t3) = (term18 t1 t2 t3).
Proof. exact (SYM (@lem4869114 t1 t2 t3)). Qed.
Lemma lem4869117 (p : Prop) : p = (term20 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4869118 {A : Type'} (P : type686 A) : (term21 A P) = (term22 A P).
Proof. exact (@lem4869117 (term21 A P)). Qed.
Lemma lem4869119 {A : Type'} (P : type686 A) : (term22 A P) = (term21 A P).
Proof. exact (SYM (@lem4869118 A P)). Qed.
Lemma lem4869120 {A : Type'} (P : type686 A) (h1 : term23 A P) : term23 A P.
Proof. exact (h1). Qed.
Lemma lem4869121 {A : Type'} : term24 A.
Proof. exact (@lem4858424 A). Qed.
Lemma lem4869125 {A : Type'} (P : type686 A) (h1 : term25 A P) : term25 A P.
Proof. exact (h1). Qed.
Lemma lem4869126 {A : Type'} (P : type686 A) : term26 A P.
Proof. exact (fun h0 : term25 A P => @lem4869125 A P h0). Qed.
Lemma lem4869127 {A : Type'} (P : type686 A) (h1 : term26 A P) : term26 A P.
Proof. exact (h1). Qed.
Lemma lem4869128 {A : Type'} (P : type686 A) (h1 : term25 A P) : term25 A P.
Proof. exact (h1). Qed.
Lemma lem4869129 {A : Type'} (P : type686 A) (h1 : term25 A P) (h2 : term26 A P) : term25 A P.
Proof. exact (@lem4869127 A P h2 (@lem4869128 A P h1)). Qed.
Lemma lem4869130 {A : Type'} (P : type686 A) (h1 : term25 A P) : term27 A P.
Proof. exact (fun h0 : term26 A P => @lem4869129 A P h1 h0). Qed.
Lemma lem4869131 {A : Type'} (P : type686 A) (h1 : term26 A P) : term26 A P.
Proof. exact (h1). Qed.
Lemma lem4869132 {A : Type'} (P : type686 A) (h1 : term25 A P) (h2 : term26 A P) : term25 A P.
Proof. exact (@lem4869130 A P h1 (@lem4869131 A P h2)). Qed.
Lemma lem4869133 {A : Type'} (P : type686 A) (h1 : term26 A P) : term26 A P.
Proof. exact (fun h0 : term25 A P => @lem4869132 A P h0 h1). Qed.
Lemma lem4869134 {A : Type'} (P : type686 A) : term28 A P.
Proof. exact (fun h0 : term26 A P => @lem4869133 A P h0). Qed.
Lemma lem4869137 {A : Type'} (P : type686 A) : term26 A P.
Proof. exact (@lem4869134 A P (@lem4869126 A P)). Qed.
Lemma lem4869138 {A : Type'} (P : type686 A) : term26 A P.
Proof. exact (@lem4869137 A P). Qed.
Lemma lem4869172 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4869173 {A : Type'} : (term29 A) = (term30 A).
Proof. exact (@lem4869172 (term24 A)). Qed.
Lemma lem4869184 {A : Type'} (P : type686 A) : (term31 A P) = (term31 A P).
Proof. exact (eq_refl (term31 A P)). Qed.
Lemma lem4869185 {A : Type'} (P : type686 A) : (term25 A P) = (term32 A P).
Proof. exact (MK_COMB (@lem4869184 A P) (@lem4869173 A)). Qed.
Lemma lem4869188 {A : Type'} : (term33 A) = (term34 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4869185 A P)). Qed.
Lemma lem4869189 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4869198 {A : Type'} : (term35 A) = (term36 A).
Proof. exact (MK_COMB (@lem4869189 A) (@lem4869188 A)). Qed.
Lemma lem4869203 {A : Type'} (P : type686 A) (s : A -> Prop) : (term37 A P s) = (term37 A P s).
Proof. exact (eq_refl (term37 A P s)). Qed.
Lemma lem4869204 {A : Type'} (P : type686 A) : (term38 A P) = (term38 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4869203 A P s)). Qed.
Lemma lem4869205 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4869206 {A : Type'} (P : type686 A) : (term39 A P) = (term39 A P).
Proof. exact (MK_COMB (@lem4869205 A) (@lem4869204 A P)). Qed.
Lemma lem4869207 {A : Type'} : (term40 A) = (term40 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4869206 A P)). Qed.
Lemma lem4869208 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4869209 {A : Type'} : (term24 A) = (term24 A).
Proof. exact (MK_COMB (@lem4869208 A) (@lem4869207 A)). Qed.
Lemma lem4869210 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4869211 {A : Type'} : (term30 A) = (term30 A).
Proof. exact (MK_COMB (@lem4869210) (@lem4869209 A)). Qed.
Lemma lem4869220 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term41 A P s t) = (term41 A P s t).
Proof. exact (eq_refl (term41 A P s t)). Qed.
Lemma lem4869221 {A : Type'} (P : type686 A) (s : A -> Prop) : (term42 A P s) = (term42 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4869220 A P s t)). Qed.
Lemma lem4869222 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4869223 {A : Type'} (P : type686 A) (s : A -> Prop) : (term43 A P s) = (term43 A P s).
Proof. exact (MK_COMB (@lem4869222 A) (@lem4869221 A P s)). Qed.
Lemma lem4869224 {A : Type'} (P : type686 A) : (term44 A P) = (term44 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4869223 A P s)). Qed.
Lemma lem4869225 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4869226 {A : Type'} (P : type686 A) : (term45 A P) = (term45 A P).
Proof. exact (MK_COMB (@lem4869225 A) (@lem4869224 A P)). Qed.
Lemma lem4869235 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term46 A P s t) = (term46 A P s t).
Proof. exact (eq_refl (term46 A P s t)). Qed.
Lemma lem4869236 {A : Type'} (P : type686 A) (s : A -> Prop) : (term47 A P s) = (term47 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4869235 A P s t)). Qed.
Lemma lem4869237 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4869238 {A : Type'} (P : type686 A) (s : A -> Prop) : (term48 A P s) = (term48 A P s).
Proof. exact (MK_COMB (@lem4869237 A) (@lem4869236 A P s)). Qed.
Lemma lem4869239 {A : Type'} (P : type686 A) : (term49 A P) = (term49 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4869238 A P s)). Qed.
Lemma lem4869240 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4869241 {A : Type'} (P : type686 A) : (term50 A P) = (term50 A P).
Proof. exact (MK_COMB (@lem4869240 A) (@lem4869239 A P)). Qed.
Lemma lem4869242 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4869243 {A : Type'} (P : type686 A) : (term51 A P) = (term51 A P).
Proof. exact (MK_COMB (@lem4869242) (@lem4869241 A P)). Qed.
Lemma lem4869244 {A : Type'} (P : type686 A) : (term21 A P) = (term21 A P).
Proof. exact (MK_COMB (@lem4869243 A P) (@lem4869226 A P)). Qed.
Lemma lem4869245 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4869246 {A : Type'} (P : type686 A) : (term23 A P) = (term23 A P).
Proof. exact (MK_COMB (@lem4869245) (@lem4869244 A P)). Qed.
Lemma lem4869247 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4869248 {A : Type'} (P : type686 A) : (term31 A P) = (term31 A P).
Proof. exact (MK_COMB (@lem4869247) (@lem4869246 A P)). Qed.
Lemma lem4869249 {A : Type'} (P : type686 A) : (term32 A P) = (term32 A P).
Proof. exact (MK_COMB (@lem4869248 A P) (@lem4869211 A)). Qed.
Lemma lem4869250 {A : Type'} : (term34 A) = (term34 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4869249 A P)). Qed.
Lemma lem4869251 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4869252 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (MK_COMB (@lem4869251 A) (@lem4869250 A)). Qed.
Lemma lem4869311 {A : Type'} : (term35 A) = (term36 A).
Proof. exact (TRANS (@lem4869198 A) (@lem4869252 A)). Qed.
Lemma lem4869312 {A : Type'} : (term36 A) = (term35 A).
Proof. exact (SYM (@lem4869311 A)). Qed.
Lemma lem4869313 {A : Type'} (P : type686 A) (h1 : term23 A P) : term23 A P.
Proof. exact (h1). Qed.
Lemma lem4869314 {A : Type'} (h1 : term24 A) : term24 A.
Proof. exact (h1). Qed.
Lemma lem4869321 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term52 A s P t) = (term53 A s P t).
Proof. exact (@lem17045 (@UNION_OF A (@ARBITRARY A) P s) (@UNION_OF A (@ARBITRARY A) P t)). Qed.
Lemma lem4869322 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term54 A P s t) = (term54 A P s t).
Proof. exact (eq_refl (term54 A P s t)). Qed.
Lemma lem4869323 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4869324 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term55 A s P t) = (term56 A s P t).
Proof. exact (MK_COMB (@lem4869323) (@lem4869321 A s P t)). Qed.
Lemma lem4869325 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term57 A P s t) = (term58 A P s t).
Proof. exact (MK_COMB (@lem4869324 A s P t) (@lem4869322 A P s t)). Qed.
Lemma lem4869326 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term46 A P s t) = (term57 A P s t).
Proof. exact (@lem17265 (term59 A s P t) (term54 A P s t)). Qed.
Lemma lem4869327 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term46 A P s t) = (term58 A P s t).
Proof. exact (TRANS (@lem4869326 A P s t) (@lem4869325 A P s t)). Qed.
Lemma lem4869328 {A : Type'} (P : type686 A) (s : A -> Prop) : (term47 A P s) = (term60 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4869327 A P s t)). Qed.
Lemma lem4869329 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4869330 {A : Type'} (P : type686 A) (s : A -> Prop) : (term48 A P s) = (term61 A P s).
Proof. exact (MK_COMB (@lem4869329 A) (@lem4869328 A P s)). Qed.
Lemma lem4869331 {A : Type'} (P : type686 A) : (term49 A P) = (term62 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4869330 A P s)). Qed.
Lemma lem4869332 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4869333 {A : Type'} (P : type686 A) : (term50 A P) = (term63 A P).
Proof. exact (MK_COMB (@lem4869332 A) (@lem4869331 A P)). Qed.
Lemma lem4869344 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term64 A P s t) = (term65 A P s t).
Proof. exact (@lem17362 (term66 A s P t) (term54 A P s t)). Qed.
Lemma lem4869345 {A : Type'} (P : type686 A) : (term67 A P) = (term68 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4869346 {A : Type'} (P : type686 A) (s : A -> Prop) : (term69 A P s) = (term70 A P s).
Proof. exact (@lem4869345 A (term42 A P s)). Qed.
Lemma lem4869347 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term71 A P s t) = (term41 A P s t).
Proof. exact (eq_refl (term71 A P s t)). Qed.
Lemma lem4869348 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4869349 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term72 A P s t) = (term64 A P s t).
Proof. exact (MK_COMB (@lem4869348) (@lem4869347 A P s t)). Qed.
Lemma lem4869350 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term72 A P s t) = (term65 A P s t).
Proof. exact (TRANS (@lem4869349 A P s t) (@lem4869344 A P s t)). Qed.
Lemma lem4869351 {A : Type'} (P : type686 A) (s : A -> Prop) : (term73 A P s) = (term74 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4869350 A P s t)). Qed.
Lemma lem4869352 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4869353 {A : Type'} (P : type686 A) (s : A -> Prop) : (term70 A P s) = (term75 A P s).
Proof. exact (MK_COMB (@lem4869352 A) (@lem4869351 A P s)). Qed.
Lemma lem4869354 {A : Type'} (P : type686 A) (s : A -> Prop) : (term69 A P s) = (term75 A P s).
Proof. exact (TRANS (@lem4869346 A P s) (@lem4869353 A P s)). Qed.
Lemma lem4869355 {A : Type'} (P : type686 A) : (term67 A P) = (term68 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4869356 {A : Type'} (P : type686 A) : (term76 A P) = (term77 A P).
Proof. exact (@lem4869355 A (term44 A P)). Qed.
Lemma lem4869357 {A : Type'} (P : type686 A) (s : A -> Prop) : (term78 A P s) = (term43 A P s).
Proof. exact (eq_refl (term78 A P s)). Qed.
Lemma lem4869358 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4869359 {A : Type'} (P : type686 A) (s : A -> Prop) : (term79 A P s) = (term69 A P s).
Proof. exact (MK_COMB (@lem4869358) (@lem4869357 A P s)). Qed.
Lemma lem4869360 {A : Type'} (P : type686 A) (s : A -> Prop) : (term79 A P s) = (term75 A P s).
Proof. exact (TRANS (@lem4869359 A P s) (@lem4869354 A P s)). Qed.
Lemma lem4869361 {A : Type'} (P : type686 A) : (term80 A P) = (term81 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4869360 A P s)). Qed.
Lemma lem4869362 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4869363 {A : Type'} (P : type686 A) : (term77 A P) = (term82 A P).
Proof. exact (MK_COMB (@lem4869362 A) (@lem4869361 A P)). Qed.
Lemma lem4869364 {A : Type'} (P : type686 A) : (term76 A P) = (term82 A P).
Proof. exact (TRANS (@lem4869356 A P) (@lem4869363 A P)). Qed.
Lemma lem4869365 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4869366 {A : Type'} (P : type686 A) : (term83 A P) = (term84 A P).
Proof. exact (MK_COMB (@lem4869365) (@lem4869333 A P)). Qed.
Lemma lem4869367 {A : Type'} (P : type686 A) : (term85 A P) = (term86 A P).
Proof. exact (MK_COMB (@lem4869366 A P) (@lem4869364 A P)). Qed.
Lemma lem4869368 {A : Type'} (P : type686 A) : (term23 A P) = (term85 A P).
Proof. exact (@lem17362 (term50 A P) (term45 A P)). Qed.
Lemma lem4869369 {A : Type'} (P : type686 A) : (term23 A P) = (term86 A P).
Proof. exact (TRANS (@lem4869368 A P) (@lem4869367 A P)). Qed.
Lemma lem4869476 {A : Type'} (P : Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4869477 {A : Type'} (P : Prop) (Q : type686 A) : (term89 A P Q) = (term90 A P Q).
Proof. exact (@lem4869476 (A -> Prop) P Q). Qed.
Lemma lem4869478 {A : Type'} (P : type686 A) : (term91 A P) = (term92 A P).
Proof. exact (@lem4869477 A (term63 A P) (term81 A P)). Qed.
Lemma lem4869479 {A : Type'} (P : type686 A) (s : A -> Prop) : (term93 A P s) = (term75 A P s).
Proof. exact (eq_refl (term93 A P s)). Qed.
Lemma lem4869480 {A : Type'} (P : type686 A) : (term94 A P) = (term81 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4869479 A P s)). Qed.
Lemma lem4869481 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4869482 {A : Type'} (P : type686 A) : (term95 A P) = (term82 A P).
Proof. exact (MK_COMB (@lem4869481 A) (@lem4869480 A P)). Qed.
Lemma lem4869483 {A : Type'} (P : type686 A) : (term84 A P) = (term84 A P).
Proof. exact (eq_refl (term84 A P)). Qed.
Lemma lem4869484 {A : Type'} (P : type686 A) : (term91 A P) = (term86 A P).
Proof. exact (MK_COMB (@lem4869483 A P) (@lem4869482 A P)). Qed.
Lemma lem4869485 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4869486 {A : Type'} (P : type686 A) : (term96 A P) = (term97 A P).
Proof. exact (MK_COMB (@lem4869485) (@lem4869484 A P)). Qed.
Lemma lem4869487 {A : Type'} (P : type686 A) (s : A -> Prop) : (term93 A P s) = (term75 A P s).
Proof. exact (eq_refl (term93 A P s)). Qed.
Lemma lem4869488 {A : Type'} (P : type686 A) : (term84 A P) = (term84 A P).
Proof. exact (eq_refl (term84 A P)). Qed.
Lemma lem4869489 {A : Type'} (P : type686 A) (s : A -> Prop) : (term98 A P s) = (term99 A P s).
Proof. exact (MK_COMB (@lem4869488 A P) (@lem4869487 A P s)). Qed.
Lemma lem4869490 {A : Type'} (P : type686 A) : (term100 A P) = (term101 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4869489 A P s)). Qed.
Lemma lem4869491 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4869492 {A : Type'} (P : type686 A) : (term92 A P) = (term102 A P).
Proof. exact (MK_COMB (@lem4869491 A) (@lem4869490 A P)). Qed.
Lemma lem4869493 {A : Type'} (P : type686 A) : ((term91 A P) = (term92 A P)) = ((term86 A P) = (term102 A P)).
Proof. exact (MK_COMB (@lem4869486 A P) (@lem4869492 A P)). Qed.
Lemma lem4869494 {A : Type'} (P : type686 A) : (term86 A P) = (term102 A P).
Proof. exact (EQ_MP (@lem4869493 A P) (@lem4869478 A P)). Qed.
Lemma lem4869496 {A : Type'} (P : Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4869497 {A : Type'} (P : Prop) (Q : type686 A) : (term89 A P Q) = (term90 A P Q).
Proof. exact (@lem4869496 (A -> Prop) P Q). Qed.
Lemma lem4869498 {A : Type'} (P : type686 A) (s : A -> Prop) : (term103 A P s) = (term104 A P s).
Proof. exact (@lem4869497 A (term63 A P) (term74 A P s)). Qed.
Lemma lem4869499 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term105 A P s t) = (term65 A P s t).
Proof. exact (eq_refl (term105 A P s t)). Qed.
Lemma lem4869500 {A : Type'} (P : type686 A) (s : A -> Prop) : (term106 A P s) = (term74 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4869499 A P s t)). Qed.
Lemma lem4869501 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4869502 {A : Type'} (P : type686 A) (s : A -> Prop) : (term107 A P s) = (term75 A P s).
Proof. exact (MK_COMB (@lem4869501 A) (@lem4869500 A P s)). Qed.
Lemma lem4869503 {A : Type'} (P : type686 A) : (term84 A P) = (term84 A P).
Proof. exact (eq_refl (term84 A P)). Qed.
Lemma lem4869504 {A : Type'} (P : type686 A) (s : A -> Prop) : (term103 A P s) = (term99 A P s).
Proof. exact (MK_COMB (@lem4869503 A P) (@lem4869502 A P s)). Qed.
Lemma lem4869505 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4869506 {A : Type'} (P : type686 A) (s : A -> Prop) : (term108 A P s) = (term109 A P s).
Proof. exact (MK_COMB (@lem4869505) (@lem4869504 A P s)). Qed.
Lemma lem4869507 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term105 A P s t) = (term65 A P s t).
Proof. exact (eq_refl (term105 A P s t)). Qed.
Lemma lem4869508 {A : Type'} (P : type686 A) : (term84 A P) = (term84 A P).
Proof. exact (eq_refl (term84 A P)). Qed.
Lemma lem4869509 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term110 A P s t) = (term111 A P s t).
Proof. exact (MK_COMB (@lem4869508 A P) (@lem4869507 A P s t)). Qed.
Lemma lem4869510 {A : Type'} (P : type686 A) (s : A -> Prop) : (term112 A P s) = (term113 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4869509 A P s t)). Qed.
Lemma lem4869511 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4869512 {A : Type'} (P : type686 A) (s : A -> Prop) : (term104 A P s) = (term114 A P s).
Proof. exact (MK_COMB (@lem4869511 A) (@lem4869510 A P s)). Qed.
Lemma lem4869513 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term103 A P s) = (term104 A P s)) = ((term99 A P s) = (term114 A P s)).
Proof. exact (MK_COMB (@lem4869506 A P s) (@lem4869512 A P s)). Qed.
Lemma lem4869514 {A : Type'} (P : type686 A) (s : A -> Prop) : (term99 A P s) = (term114 A P s).
Proof. exact (EQ_MP (@lem4869513 A P s) (@lem4869498 A P s)). Qed.
Lemma lem4869515 {A : Type'} (P : type686 A) : (term101 A P) = (term115 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4869514 A P s)). Qed.
Lemma lem4869516 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4869517 {A : Type'} (P : type686 A) : (term102 A P) = (term116 A P).
Proof. exact (MK_COMB (@lem4869516 A) (@lem4869515 A P)). Qed.
Lemma lem4869519 {A : Type'} (P : type686 A) : (term86 A P) = (term116 A P).
Proof. exact (TRANS (@lem4869494 A P) (@lem4869517 A P)). Qed.
Lemma lem4869520 {A : Type'} (P : type686 A) : (term23 A P) = (term116 A P).
Proof. exact (TRANS (@lem4869369 A P) (@lem4869519 A P)). Qed.
Lemma lem4869521 {A : Type'} (P : type686 A) (h1 : term23 A P) : term116 A P.
Proof. exact (EQ_MP (@lem4869520 A P) (@lem4869313 A P h1)). Qed.
Lemma lem4869528 {A : Type'} (P : type686 A) (s : A -> Prop) : (term37 A P s) = (term117 A P s).
Proof. exact (@lem17265 (P s) (@UNION_OF A (@ARBITRARY A) P s)). Qed.
Lemma lem4869529 {A : Type'} (P : type686 A) : (term38 A P) = (term118 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4869528 A P s)). Qed.
Lemma lem4869530 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4869531 {A : Type'} (P : type686 A) : (term39 A P) = (term119 A P).
Proof. exact (MK_COMB (@lem4869530 A) (@lem4869529 A P)). Qed.
Lemma lem4869532 {A : Type'} : (term40 A) = (term120 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4869531 A P)). Qed.
Lemma lem4869533 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4869590 {A : Type'} : (term24 A) = (term121 A).
Proof. exact (MK_COMB (@lem4869533 A) (@lem4869532 A)). Qed.
Lemma lem4869591 {A : Type'} (h1 : term24 A) : term121 A.
Proof. exact (EQ_MP (@lem4869590 A) (@lem4869314 A h1)). Qed.
Lemma lem4869592 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term114 A P s) : term114 A P s.
Proof. exact (h1). Qed.
Lemma lem4869593 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term111 A P s t.
Proof. exact (h1). Qed.
Lemma lem4869602 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4869603 {A : Type'} (f : type74 A) (x : type180 A) : (f x) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4869602 (type180 A) (type174 A) f x). Qed.
Lemma lem4869604 {A : Type'} : (@UNION_OF A (@ARBITRARY A)) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A)).
Proof. exact (@lem4869603 A (@UNION_OF A) (@ARBITRARY A)). Qed.
Lemma lem4869605 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4869606 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A) P).
Proof. exact (MK_COMB (@lem4869604 A) (@lem4869605 A P)). Qed.
Lemma lem4869608 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4869609 {A : Type'} (f : type174 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4869608 (type686 A) (type686 A) f x). Qed.
Lemma lem4869610 {A : Type'} (P : type686 A) : (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A) P) = (term122 A P).
Proof. exact (@lem4869609 A (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A)) P). Qed.
Lemma lem4869611 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (term122 A P).
Proof. exact (TRANS (@lem4869606 A P) (@lem4869610 A P)). Qed.
Lemma lem4869612 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4869613 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@ARBITRARY A) P s) = (term123 A P s).
Proof. exact (MK_COMB (@lem4869611 A P) (@lem4869612 A s)). Qed.
Lemma lem4869615 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4869616 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4869615 (A -> Prop) Prop f x). Qed.
Lemma lem4869617 {A : Type'} (P : type686 A) (s : A -> Prop) : (term123 A P s) = (term124 A P s).
Proof. exact (@lem4869616 A (term122 A P) s). Qed.
Lemma lem4869619 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@ARBITRARY A) P s) = (term124 A P s).
Proof. exact (TRANS (@lem4869613 A P s) (@lem4869617 A P s)). Qed.
Lemma lem4869620 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4869625 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4869626 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4869625 (A -> Prop) Prop f x). Qed.
Lemma lem4869628 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = (@I ((A -> Prop) -> Prop) P s).
Proof. exact (@lem4869626 A P s). Qed.
Lemma lem4869629 {A : Type'} (P : type686 A) (s : A -> Prop) : (term125 A P s) = (term126 A P s).
Proof. exact (MK_COMB (@lem4869620) (@lem4869628 A P s)). Qed.
Lemma lem4869630 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4869631 {A : Type'} (P : type686 A) (s : A -> Prop) : (term127 A P s) = (term128 A P s).
Proof. exact (MK_COMB (@lem4869630) (@lem4869629 A P s)). Qed.
Lemma lem4869632 {A : Type'} (P : type686 A) (s : A -> Prop) : (term117 A P s) = (term129 A P s).
Proof. exact (MK_COMB (@lem4869631 A P s) (@lem4869619 A P s)). Qed.
Lemma lem4869633 {A : Type'} (P : type686 A) : (term118 A P) = (term130 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4869632 A P s)). Qed.
Lemma lem4869634 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4869635 {A : Type'} (P : type686 A) : (term119 A P) = (term131 A P).
Proof. exact (MK_COMB (@lem4869634 A) (@lem4869633 A P)). Qed.
Lemma lem4869636 {A : Type'} : (term120 A) = (term132 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4869635 A P)). Qed.
Lemma lem4869637 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4869638 {A : Type'} : (term121 A) = (term133 A).
Proof. exact (MK_COMB (@lem4869637 A) (@lem4869636 A)). Qed.
Lemma lem4869639 {A : Type'} (h1 : term24 A) : term133 A.
Proof. exact (EQ_MP (@lem4869638 A) (@lem4869591 A h1)). Qed.
Lemma lem4869640 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4869650 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4869651 {A : Type'} (f : type636 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4869650 (A -> Prop) (type672 A) f x). Qed.
Lemma lem4869652 {A : Type'} (s : A -> Prop) : (@INTER A s) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s).
Proof. exact (@lem4869651 A (@INTER A) s). Qed.
Lemma lem4869653 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4869654 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@INTER A s t) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s t).
Proof. exact (MK_COMB (@lem4869652 A s) (@lem4869653 A t)). Qed.
Lemma lem4869656 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4869657 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4869656 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem4869658 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s t) = (term134 A s t).
Proof. exact (@lem4869657 A (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s) t). Qed.
Lemma lem4869660 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@INTER A s t) = (term134 A s t).
Proof. exact (TRANS (@lem4869654 A s t) (@lem4869658 A s t)). Qed.
Lemma lem4869662 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (@UNION_OF A (@ARBITRARY A) P).
Proof. exact (eq_refl (@UNION_OF A (@ARBITRARY A) P)). Qed.
Lemma lem4869663 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term54 A P s t) = (term135 A P s t).
Proof. exact (MK_COMB (@lem4869662 A P) (@lem4869660 A s t)). Qed.
Lemma lem4869665 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4869666 {A : Type'} (f : type74 A) (x : type180 A) : (f x) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4869665 (type180 A) (type174 A) f x). Qed.
Lemma lem4869667 {A : Type'} : (@UNION_OF A (@ARBITRARY A)) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A)).
Proof. exact (@lem4869666 A (@UNION_OF A) (@ARBITRARY A)). Qed.
Lemma lem4869668 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4869669 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A) P).
Proof. exact (MK_COMB (@lem4869667 A) (@lem4869668 A P)). Qed.
Lemma lem4869671 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4869672 {A : Type'} (f : type174 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4869671 (type686 A) (type686 A) f x). Qed.
Lemma lem4869673 {A : Type'} (P : type686 A) : (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A) P) = (term122 A P).
Proof. exact (@lem4869672 A (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A)) P). Qed.
Lemma lem4869674 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (term122 A P).
Proof. exact (TRANS (@lem4869669 A P) (@lem4869673 A P)). Qed.
Lemma lem4869675 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term134 A s t) = (term134 A s t).
Proof. exact (eq_refl (term134 A s t)). Qed.
Lemma lem4869676 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term135 A P s t) = (term136 A P s t).
Proof. exact (MK_COMB (@lem4869674 A P) (@lem4869675 A s t)). Qed.
Lemma lem4869678 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4869679 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4869678 (A -> Prop) Prop f x). Qed.
Lemma lem4869680 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term136 A P s t) = (term137 A P s t).
Proof. exact (@lem4869679 A (term122 A P) (term134 A s t)). Qed.
Lemma lem4869681 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term135 A P s t) = (term137 A P s t).
Proof. exact (TRANS (@lem4869676 A P s t) (@lem4869680 A P s t)). Qed.
Lemma lem4869682 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term54 A P s t) = (term137 A P s t).
Proof. exact (TRANS (@lem4869663 A P s t) (@lem4869681 A P s t)). Qed.
Lemma lem4869683 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term138 A P s t) = (term139 A P s t).
Proof. exact (MK_COMB (@lem4869640) (@lem4869682 A P s t)). Qed.
Lemma lem4869688 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4869689 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4869688 (A -> Prop) Prop f x). Qed.
Lemma lem4869691 {A : Type'} (P : type686 A) (t : A -> Prop) : (P t) = (@I ((A -> Prop) -> Prop) P t).
Proof. exact (@lem4869689 A P t). Qed.
Lemma lem4869696 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4869697 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4869696 (A -> Prop) Prop f x). Qed.
Lemma lem4869699 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = (@I ((A -> Prop) -> Prop) P s).
Proof. exact (@lem4869697 A P s). Qed.
Lemma lem4869700 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4869701 {A : Type'} (P : type686 A) (s : A -> Prop) : (term140 A P s) = (term141 A P s).
Proof. exact (MK_COMB (@lem4869700) (@lem4869699 A P s)). Qed.
Lemma lem4869702 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term66 A s P t) = (term142 A s P t).
Proof. exact (MK_COMB (@lem4869701 A P s) (@lem4869691 A P t)). Qed.
Lemma lem4869703 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4869704 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term143 A s P t) = (term144 A s P t).
Proof. exact (MK_COMB (@lem4869703) (@lem4869702 A s P t)). Qed.
Lemma lem4869705 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term65 A P s t) = (term145 A P s t).
Proof. exact (MK_COMB (@lem4869704 A s P t) (@lem4869683 A P s t)). Qed.
Lemma lem4869715 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4869716 {A : Type'} (f : type636 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4869715 (A -> Prop) (type672 A) f x). Qed.
Lemma lem4869717 {A : Type'} (s : A -> Prop) : (@INTER A s) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s).
Proof. exact (@lem4869716 A (@INTER A) s). Qed.
Lemma lem4869718 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4869719 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@INTER A s t) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s t).
Proof. exact (MK_COMB (@lem4869717 A s) (@lem4869718 A t)). Qed.
Lemma lem4869721 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4869722 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4869721 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem4869723 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s t) = (term134 A s t).
Proof. exact (@lem4869722 A (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s) t). Qed.
Lemma lem4869725 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@INTER A s t) = (term134 A s t).
Proof. exact (TRANS (@lem4869719 A s t) (@lem4869723 A s t)). Qed.
Lemma lem4869727 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (@UNION_OF A (@ARBITRARY A) P).
Proof. exact (eq_refl (@UNION_OF A (@ARBITRARY A) P)). Qed.
Lemma lem4869728 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term54 A P s t) = (term135 A P s t).
Proof. exact (MK_COMB (@lem4869727 A P) (@lem4869725 A s t)). Qed.
Lemma lem4869730 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4869731 {A : Type'} (f : type74 A) (x : type180 A) : (f x) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4869730 (type180 A) (type174 A) f x). Qed.
Lemma lem4869732 {A : Type'} : (@UNION_OF A (@ARBITRARY A)) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A)).
Proof. exact (@lem4869731 A (@UNION_OF A) (@ARBITRARY A)). Qed.
Lemma lem4869733 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4869734 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A) P).
Proof. exact (MK_COMB (@lem4869732 A) (@lem4869733 A P)). Qed.
Lemma lem4869736 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4869737 {A : Type'} (f : type174 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4869736 (type686 A) (type686 A) f x). Qed.
Lemma lem4869738 {A : Type'} (P : type686 A) : (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A) P) = (term122 A P).
Proof. exact (@lem4869737 A (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A)) P). Qed.
Lemma lem4869739 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (term122 A P).
Proof. exact (TRANS (@lem4869734 A P) (@lem4869738 A P)). Qed.
Lemma lem4869740 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term134 A s t) = (term134 A s t).
Proof. exact (eq_refl (term134 A s t)). Qed.
Lemma lem4869741 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term135 A P s t) = (term136 A P s t).
Proof. exact (MK_COMB (@lem4869739 A P) (@lem4869740 A s t)). Qed.
Lemma lem4869743 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4869744 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4869743 (A -> Prop) Prop f x). Qed.
Lemma lem4869745 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term136 A P s t) = (term137 A P s t).
Proof. exact (@lem4869744 A (term122 A P) (term134 A s t)). Qed.
Lemma lem4869746 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term135 A P s t) = (term137 A P s t).
Proof. exact (TRANS (@lem4869741 A P s t) (@lem4869745 A P s t)). Qed.
Lemma lem4869747 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term54 A P s t) = (term137 A P s t).
Proof. exact (TRANS (@lem4869728 A P s t) (@lem4869746 A P s t)). Qed.
Lemma lem4869748 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4869757 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4869758 {A : Type'} (f : type74 A) (x : type180 A) : (f x) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4869757 (type180 A) (type174 A) f x). Qed.
Lemma lem4869759 {A : Type'} : (@UNION_OF A (@ARBITRARY A)) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A)).
Proof. exact (@lem4869758 A (@UNION_OF A) (@ARBITRARY A)). Qed.
Lemma lem4869760 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4869761 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A) P).
Proof. exact (MK_COMB (@lem4869759 A) (@lem4869760 A P)). Qed.
Lemma lem4869763 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4869764 {A : Type'} (f : type174 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4869763 (type686 A) (type686 A) f x). Qed.
Lemma lem4869765 {A : Type'} (P : type686 A) : (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A) P) = (term122 A P).
Proof. exact (@lem4869764 A (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A)) P). Qed.
Lemma lem4869766 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (term122 A P).
Proof. exact (TRANS (@lem4869761 A P) (@lem4869765 A P)). Qed.
Lemma lem4869767 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4869768 {A : Type'} (P : type686 A) (t : A -> Prop) : (@UNION_OF A (@ARBITRARY A) P t) = (term123 A P t).
Proof. exact (MK_COMB (@lem4869766 A P) (@lem4869767 A t)). Qed.
Lemma lem4869770 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4869771 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4869770 (A -> Prop) Prop f x). Qed.
Lemma lem4869772 {A : Type'} (P : type686 A) (t : A -> Prop) : (term123 A P t) = (term124 A P t).
Proof. exact (@lem4869771 A (term122 A P) t). Qed.
Lemma lem4869774 {A : Type'} (P : type686 A) (t : A -> Prop) : (@UNION_OF A (@ARBITRARY A) P t) = (term124 A P t).
Proof. exact (TRANS (@lem4869768 A P t) (@lem4869772 A P t)). Qed.
Lemma lem4869775 {A : Type'} (P : type686 A) (t : A -> Prop) : (term146 A P t) = (term147 A P t).
Proof. exact (MK_COMB (@lem4869748) (@lem4869774 A P t)). Qed.
Lemma lem4869776 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4869785 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4869786 {A : Type'} (f : type74 A) (x : type180 A) : (f x) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4869785 (type180 A) (type174 A) f x). Qed.
Lemma lem4869787 {A : Type'} : (@UNION_OF A (@ARBITRARY A)) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A)).
Proof. exact (@lem4869786 A (@UNION_OF A) (@ARBITRARY A)). Qed.
Lemma lem4869788 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4869789 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A) P).
Proof. exact (MK_COMB (@lem4869787 A) (@lem4869788 A P)). Qed.
Lemma lem4869791 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4869792 {A : Type'} (f : type174 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4869791 (type686 A) (type686 A) f x). Qed.
Lemma lem4869793 {A : Type'} (P : type686 A) : (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A) P) = (term122 A P).
Proof. exact (@lem4869792 A (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A)) P). Qed.
Lemma lem4869794 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (term122 A P).
Proof. exact (TRANS (@lem4869789 A P) (@lem4869793 A P)). Qed.
Lemma lem4869795 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4869796 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@ARBITRARY A) P s) = (term123 A P s).
Proof. exact (MK_COMB (@lem4869794 A P) (@lem4869795 A s)). Qed.
Lemma lem4869798 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4869799 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4869798 (A -> Prop) Prop f x). Qed.
Lemma lem4869800 {A : Type'} (P : type686 A) (s : A -> Prop) : (term123 A P s) = (term124 A P s).
Proof. exact (@lem4869799 A (term122 A P) s). Qed.
Lemma lem4869802 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@ARBITRARY A) P s) = (term124 A P s).
Proof. exact (TRANS (@lem4869796 A P s) (@lem4869800 A P s)). Qed.
Lemma lem4869803 {A : Type'} (P : type686 A) (s : A -> Prop) : (term146 A P s) = (term147 A P s).
Proof. exact (MK_COMB (@lem4869776) (@lem4869802 A P s)). Qed.
Lemma lem4869804 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4869805 {A : Type'} (P : type686 A) (s : A -> Prop) : (term148 A P s) = (term149 A P s).
Proof. exact (MK_COMB (@lem4869804) (@lem4869803 A P s)). Qed.
Lemma lem4869806 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term53 A s P t) = (term150 A s P t).
Proof. exact (MK_COMB (@lem4869805 A P s) (@lem4869775 A P t)). Qed.
Lemma lem4869807 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4869808 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term56 A s P t) = (term151 A s P t).
Proof. exact (MK_COMB (@lem4869807) (@lem4869806 A s P t)). Qed.
Lemma lem4869809 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term58 A P s t) = (term152 A P s t).
Proof. exact (MK_COMB (@lem4869808 A s P t) (@lem4869747 A P s t)). Qed.
Lemma lem4869810 {A : Type'} (P : type686 A) (s : A -> Prop) : (term60 A P s) = (term153 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4869809 A P s t)). Qed.
Lemma lem4869811 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4869812 {A : Type'} (P : type686 A) (s : A -> Prop) : (term61 A P s) = (term154 A P s).
Proof. exact (MK_COMB (@lem4869811 A) (@lem4869810 A P s)). Qed.
Lemma lem4869813 {A : Type'} (P : type686 A) : (term62 A P) = (term155 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4869812 A P s)). Qed.
Lemma lem4869814 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4869815 {A : Type'} (P : type686 A) : (term63 A P) = (term156 A P).
Proof. exact (MK_COMB (@lem4869814 A) (@lem4869813 A P)). Qed.
Lemma lem4869816 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4869817 {A : Type'} (P : type686 A) : (term84 A P) = (term157 A P).
Proof. exact (MK_COMB (@lem4869816) (@lem4869815 A P)). Qed.
Lemma lem4869818 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term111 A P s t) = (term158 A P s t).
Proof. exact (MK_COMB (@lem4869817 A P) (@lem4869705 A P s t)). Qed.
Lemma lem4869819 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term158 A P s t.
Proof. exact (EQ_MP (@lem4869818 A P s t) (@lem4869593 A P s t h1)). Qed.
Lemma lem4869820 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term145 A P s t.
Proof. exact (proj2 (@lem4869819 A P s t h1)). Qed.
Lemma lem4869821 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term156 A P.
Proof. exact (proj1 (@lem4869819 A P s t h1)). Qed.
Lemma lem4869823 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term142 A s P t.
Proof. exact (proj1 (@lem4869820 A P s t h1)). Qed.
Lemma lem4869833 {A : Type'} (P : type686 A) (s : A -> Prop) : (term129 A P s) = (term129 A P s).
Proof. exact (eq_refl (term129 A P s)). Qed.
Lemma lem4869834 {A : Type'} (P : type686 A) : (term130 A P) = (term130 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4869833 A P s)). Qed.
Lemma lem4869835 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4869836 {A : Type'} (P : type686 A) : (term131 A P) = (term131 A P).
Proof. exact (MK_COMB (@lem4869835 A) (@lem4869834 A P)). Qed.
Lemma lem4869837 {A : Type'} : (term132 A) = (term132 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4869836 A P)). Qed.
Lemma lem4869838 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4869840 {A : Type'} : (term133 A) = (term133 A).
Proof. exact (MK_COMB (@lem4869838 A) (@lem4869837 A)). Qed.
Lemma lem4869841 {A : Type'} (h1 : term24 A) : term133 A.
Proof. exact (EQ_MP (@lem4869840 A) (@lem4869639 A h1)). Qed.
Lemma lem4869855 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term152 A P s t) = (term152 A P s t).
Proof. exact (eq_refl (term152 A P s t)). Qed.
Lemma lem4869856 {A : Type'} (P : type686 A) (s : A -> Prop) : (term153 A P s) = (term153 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4869855 A P s t)). Qed.
Lemma lem4869857 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4869858 {A : Type'} (P : type686 A) (s : A -> Prop) : (term154 A P s) = (term154 A P s).
Proof. exact (MK_COMB (@lem4869857 A) (@lem4869856 A P s)). Qed.
Lemma lem4869859 {A : Type'} (P : type686 A) : (term155 A P) = (term155 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4869858 A P s)). Qed.
Lemma lem4869860 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4869862 {A : Type'} (P : type686 A) : (term156 A P) = (term156 A P).
Proof. exact (MK_COMB (@lem4869860 A) (@lem4869859 A P)). Qed.
Lemma lem4869863 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term156 A P.
Proof. exact (EQ_MP (@lem4869862 A P) (@lem4869821 A P s t h1)). Qed.
Lemma lem4869876 {A : Type'} (_60257 : type686 A) (h1 : term24 A) : term159 A _60257.
Proof. exact (@lem4869841 A h1 _60257). Qed.
Lemma lem4869877 {A : Type'} (_60257 : type686 A) : (term159 A _60257) = (term131 A _60257).
Proof. exact (eq_refl (term159 A _60257)). Qed.
Lemma lem4869878 {A : Type'} (_60257 : type686 A) (h1 : term24 A) : term131 A _60257.
Proof. exact (EQ_MP (@lem4869877 A _60257) (@lem4869876 A _60257 h1)). Qed.
Lemma lem4869879 {A : Type'} (_60257 : type686 A) (_60258 : A -> Prop) (h1 : term24 A) : term160 A _60257 _60258.
Proof. exact (@lem4869878 A _60257 h1 _60258). Qed.
Lemma lem4869880 {A : Type'} (_60257 : type686 A) (_60258 : A -> Prop) : (term160 A _60257 _60258) = (term129 A _60257 _60258).
Proof. exact (eq_refl (term160 A _60257 _60258)). Qed.
Lemma lem4869882 {A : Type'} (_60259 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term161 A P _60259.
Proof. exact (@lem4869863 A P s t h1 _60259). Qed.
Lemma lem4869883 {A : Type'} (P : type686 A) (_60259 : A -> Prop) : (term161 A P _60259) = (term154 A P _60259).
Proof. exact (eq_refl (term161 A P _60259)). Qed.
Lemma lem4869884 {A : Type'} (_60259 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term154 A P _60259.
Proof. exact (EQ_MP (@lem4869883 A P _60259) (@lem4869882 A _60259 P s t h1)). Qed.
Lemma lem4869885 {A : Type'} (_60259 : A -> Prop) (_60260 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term162 A P _60259 _60260.
Proof. exact (@lem4869884 A _60259 P s t h1 _60260). Qed.
Lemma lem4869886 {A : Type'} (P : type686 A) (_60259 : A -> Prop) (_60260 : A -> Prop) : (term162 A P _60259 _60260) = (term152 A P _60259 _60260).
Proof. exact (eq_refl (term162 A P _60259 _60260)). Qed.
Lemma lem4869887 {A : Type'} (_60259 : A -> Prop) (_60260 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term152 A P _60259 _60260.
Proof. exact (EQ_MP (@lem4869886 A P _60259 _60260) (@lem4869885 A _60259 _60260 P s t h1)). Qed.
Lemma lem4869893 {A : Type'} (_60257 : type686 A) (_60258 : A -> Prop) (h1 : term24 A) : term129 A _60257 _60258.
Proof. exact (EQ_MP (@lem4869880 A _60257 _60258) (@lem4869879 A _60257 _60258 h1)). Qed.
Lemma lem4869904 {A : Type'} (P : type686 A) (_60259 : A -> Prop) (_60260 : A -> Prop) : (term152 A P _60259 _60260) = (term163 A P _60259 _60260).
Proof. exact (@lem4869115 (term147 A P _60259) (term147 A P _60260) (term137 A P _60259 _60260)). Qed.
Lemma lem4869905 {A : Type'} (_60259 : A -> Prop) (_60260 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term163 A P _60259 _60260.
Proof. exact (EQ_MP (@lem4869904 A P _60259 _60260) (@lem4869887 A _60259 _60260 P s t h1)). Qed.
Lemma lem4869907 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term139 A P s t.
Proof. exact (proj2 (@lem4869820 A P s t h1)). Qed.
Lemma lem4869913 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : @I ((A -> Prop) -> Prop) P s.
Proof. exact (proj1 (@lem4869823 A P s t h1)). Qed.
Lemma lem4869914 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term164 A P s.
Proof. exact (fun h0 : term126 A P s => @lem4869913 A P s t h1). Qed.
Lemma lem4869916 (p : Prop) : (term165 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4869917 {A : Type'} (P : type686 A) (s : A -> Prop) : (term164 A P s) = (@I ((A -> Prop) -> Prop) P s).
Proof. exact (@lem4869916 (@I ((A -> Prop) -> Prop) P s)). Qed.
Lemma lem4869918 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : @I ((A -> Prop) -> Prop) P s.
Proof. exact (EQ_MP (@lem4869917 A P s) (@lem4869914 A P s t h1)). Qed.
Lemma lem4869924 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4869925 {A : Type'} (_60257 : type686 A) (_60258 : A -> Prop) : (term129 A _60257 _60258) = (term166 A _60257 _60258).
Proof. exact (@lem4869924 (term124 A _60257 _60258) (term126 A _60257 _60258)). Qed.
Lemma lem4869931 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4869932 {A : Type'} (_60257 : type686 A) (_60258 : A -> Prop) : (term167 A _60257 _60258) = (term168 A _60257 _60258).
Proof. exact (MK_COMB (@lem4869931) (@lem4869925 A _60257 _60258)). Qed.
Lemma lem4869938 {A : Type'} (_60257 : type686 A) (_60258 : A -> Prop) : (term166 A _60257 _60258) = (term166 A _60257 _60258).
Proof. exact (eq_refl (term166 A _60257 _60258)). Qed.
Lemma lem4869939 {A : Type'} (_60257 : type686 A) (_60258 : A -> Prop) : ((term129 A _60257 _60258) = (term166 A _60257 _60258)) = ((term166 A _60257 _60258) = (term166 A _60257 _60258)).
Proof. exact (MK_COMB (@lem4869932 A _60257 _60258) (@lem4869938 A _60257 _60258)). Qed.
Lemma lem4869941 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4869942 (x : Prop) : (x = x) = True.
Proof. exact (@lem4869941 Prop x). Qed.
Lemma lem4869943 {A : Type'} (_60257 : type686 A) (_60258 : A -> Prop) : ((term166 A _60257 _60258) = (term166 A _60257 _60258)) = True.
Proof. exact (@lem4869942 (term166 A _60257 _60258)). Qed.
Lemma lem4869944 {A : Type'} (_60257 : type686 A) (_60258 : A -> Prop) : ((term129 A _60257 _60258) = (term166 A _60257 _60258)) = True.
Proof. exact (TRANS (@lem4869939 A _60257 _60258) (@lem4869943 A _60257 _60258)). Qed.
Lemma lem4869945 {A : Type'} (_60257 : type686 A) (_60258 : A -> Prop) : True = ((term129 A _60257 _60258) = (term166 A _60257 _60258)).
Proof. exact (SYM (@lem4869944 A _60257 _60258)). Qed.
Lemma lem4869946 {A : Type'} (_60257 : type686 A) (_60258 : A -> Prop) : (term129 A _60257 _60258) = (term166 A _60257 _60258).
Proof. exact (EQ_MP (@lem4869945 A _60257 _60258) (@lem0)). Qed.
Lemma lem4869947 {A : Type'} (_60257 : type686 A) (_60258 : A -> Prop) (h1 : term24 A) : term166 A _60257 _60258.
Proof. exact (EQ_MP (@lem4869946 A _60257 _60258) (@lem4869893 A _60257 _60258 h1)). Qed.
Lemma lem4869949 (b : Prop) (a : Prop) : (a \/ b) = (term169 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4869950 {A : Type'} (_60257 : type686 A) (_60258 : A -> Prop) : (term166 A _60257 _60258) = (term170 A _60257 _60258).
Proof. exact (@lem4869949 (term126 A _60257 _60258) (term124 A _60257 _60258)). Qed.
Lemma lem4869952 (a : Prop) : (term171 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4869953 {A : Type'} (_60257 : type686 A) (_60258 : A -> Prop) : (term172 A _60257 _60258) = (@I ((A -> Prop) -> Prop) _60257 _60258).
Proof. exact (@lem4869952 (@I ((A -> Prop) -> Prop) _60257 _60258)). Qed.
Lemma lem4869954 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4869955 {A : Type'} (_60257 : type686 A) (_60258 : A -> Prop) : (term173 A _60257 _60258) = (term174 A _60257 _60258).
Proof. exact (MK_COMB (@lem4869954) (@lem4869953 A _60257 _60258)). Qed.
Lemma lem4869956 {A : Type'} (_60257 : type686 A) (_60258 : A -> Prop) : (term124 A _60257 _60258) = (term124 A _60257 _60258).
Proof. exact (eq_refl (term124 A _60257 _60258)). Qed.
Lemma lem4869957 {A : Type'} (_60257 : type686 A) (_60258 : A -> Prop) : (term170 A _60257 _60258) = (term175 A _60257 _60258).
Proof. exact (MK_COMB (@lem4869955 A _60257 _60258) (@lem4869956 A _60257 _60258)). Qed.
Lemma lem4869958 {A : Type'} (_60257 : type686 A) (_60258 : A -> Prop) : (term166 A _60257 _60258) = (term175 A _60257 _60258).
Proof. exact (TRANS (@lem4869950 A _60257 _60258) (@lem4869957 A _60257 _60258)). Qed.
Lemma lem4869961 {A : Type'} (_60257 : type686 A) (_60258 : A -> Prop) (h1 : term24 A) : term175 A _60257 _60258.
Proof. exact (EQ_MP (@lem4869958 A _60257 _60258) (@lem4869947 A _60257 _60258 h1)). Qed.
Lemma lem4869962 {A : Type'} (_60257 : type686 A) (_60258 : A -> Prop) (h1 : term24 A) : term175 A _60257 _60258.
Proof. exact (@lem4869961 A _60257 _60258 h1). Qed.
Lemma lem4869963 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term24 A) : term175 A P s.
Proof. exact (@lem4869962 A P s h1). Qed.
Lemma lem4869966 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term24 A) (h2 : term111 A P s t) : term124 A P s.
Proof. exact (@lem4869963 A P s h1 (@lem4869918 A P s t h2)). Qed.
Lemma lem4869967 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term24 A) (h2 : term111 A P s t) : term176 A P s.
Proof. exact (fun h0 : term147 A P s => @lem4869966 A P s t h1 h2). Qed.
Lemma lem4869969 (p : Prop) : (term165 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4869970 {A : Type'} (P : type686 A) (s : A -> Prop) : (term176 A P s) = (term124 A P s).
Proof. exact (@lem4869969 (term124 A P s)). Qed.
Lemma lem4869971 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term24 A) (h2 : term111 A P s t) : term124 A P s.
Proof. exact (EQ_MP (@lem4869970 A P s) (@lem4869967 A P s t h1 h2)). Qed.
Lemma lem4869973 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : @I ((A -> Prop) -> Prop) P t.
Proof. exact (proj2 (@lem4869823 A P s t h1)). Qed.
Lemma lem4869974 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term164 A P t.
Proof. exact (fun h0 : term126 A P t => @lem4869973 A P s t h1). Qed.
Lemma lem4869976 (p : Prop) : (term165 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4869977 {A : Type'} (P : type686 A) (t : A -> Prop) : (term164 A P t) = (@I ((A -> Prop) -> Prop) P t).
Proof. exact (@lem4869976 (@I ((A -> Prop) -> Prop) P t)). Qed.
Lemma lem4869978 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : @I ((A -> Prop) -> Prop) P t.
Proof. exact (EQ_MP (@lem4869977 A P t) (@lem4869974 A P s t h1)). Qed.
Lemma lem4869980 {A : Type'} (_60257 : type686 A) (_60258 : A -> Prop) (h1 : term24 A) : term175 A _60257 _60258.
Proof. exact (EQ_MP (@lem4869958 A _60257 _60258) (@lem4869947 A _60257 _60258 h1)). Qed.
Lemma lem4869981 {A : Type'} (_60257 : type686 A) (_60258 : A -> Prop) (h1 : term24 A) : term175 A _60257 _60258.
Proof. exact (@lem4869980 A _60257 _60258 h1). Qed.
Lemma lem4869982 {A : Type'} (P : type686 A) (t : A -> Prop) (h1 : term24 A) : term175 A P t.
Proof. exact (@lem4869981 A P t h1). Qed.
Lemma lem4869985 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term24 A) (h2 : term111 A P s t) : term124 A P t.
Proof. exact (@lem4869982 A P t h1 (@lem4869978 A P s t h2)). Qed.
Lemma lem4869986 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term24 A) (h2 : term111 A P s t) : term176 A P t.
Proof. exact (fun h0 : term147 A P t => @lem4869985 A P s t h1 h2). Qed.
Lemma lem4869988 (p : Prop) : (term165 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4869989 {A : Type'} (P : type686 A) (t : A -> Prop) : (term176 A P t) = (term124 A P t).
Proof. exact (@lem4869988 (term124 A P t)). Qed.
Lemma lem4869990 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term24 A) (h2 : term111 A P s t) : term124 A P t.
Proof. exact (EQ_MP (@lem4869989 A P t) (@lem4869986 A P s t h1 h2)). Qed.
Lemma lem4870006 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4870007 {A : Type'} (_60259 : A -> Prop) (P : type686 A) (_60260 : A -> Prop) : (term177 A P _60259 _60260) = (term178 A _60259 P _60260).
Proof. exact (@lem4870006 (term137 A P _60259 _60260) (term147 A P _60260)). Qed.
Lemma lem4870013 {A : Type'} (P : type686 A) (_60259 : A -> Prop) : (term149 A P _60259) = (term149 A P _60259).
Proof. exact (eq_refl (term149 A P _60259)). Qed.
Lemma lem4870014 {A : Type'} (_60259 : A -> Prop) (P : type686 A) (_60260 : A -> Prop) : (term163 A P _60259 _60260) = (term179 A _60259 P _60260).
Proof. exact (MK_COMB (@lem4870013 A P _60259) (@lem4870007 A _60259 P _60260)). Qed.
Lemma lem4870018 (q : Prop) (p : Prop) (r : Prop) : (term18 p q r) = (term18 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4870019 {A : Type'} (_60259 : A -> Prop) (P : type686 A) (_60260 : A -> Prop) : (term179 A _60259 P _60260) = (term180 A _60259 P _60260).
Proof. exact (@lem4870018 (term137 A P _60259 _60260) (term147 A P _60259) (term147 A P _60260)). Qed.
Lemma lem4870035 {A : Type'} (_60259 : A -> Prop) (P : type686 A) (_60260 : A -> Prop) : (term163 A P _60259 _60260) = (term180 A _60259 P _60260).
Proof. exact (TRANS (@lem4870014 A _60259 P _60260) (@lem4870019 A _60259 P _60260)). Qed.
Lemma lem4870036 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4870037 {A : Type'} (_60259 : A -> Prop) (P : type686 A) (_60260 : A -> Prop) : (term181 A P _60259 _60260) = (term182 A _60259 P _60260).
Proof. exact (MK_COMB (@lem4870036) (@lem4870035 A _60259 P _60260)). Qed.
Lemma lem4870053 {A : Type'} (_60259 : A -> Prop) (P : type686 A) (_60260 : A -> Prop) : (term180 A _60259 P _60260) = (term180 A _60259 P _60260).
Proof. exact (eq_refl (term180 A _60259 P _60260)). Qed.
Lemma lem4870054 {A : Type'} (_60259 : A -> Prop) (P : type686 A) (_60260 : A -> Prop) : ((term163 A P _60259 _60260) = (term180 A _60259 P _60260)) = ((term180 A _60259 P _60260) = (term180 A _60259 P _60260)).
Proof. exact (MK_COMB (@lem4870037 A _60259 P _60260) (@lem4870053 A _60259 P _60260)). Qed.
Lemma lem4870056 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4870057 (x : Prop) : (x = x) = True.
Proof. exact (@lem4870056 Prop x). Qed.
Lemma lem4870058 {A : Type'} (_60259 : A -> Prop) (P : type686 A) (_60260 : A -> Prop) : ((term180 A _60259 P _60260) = (term180 A _60259 P _60260)) = True.
Proof. exact (@lem4870057 (term180 A _60259 P _60260)). Qed.
Lemma lem4870059 {A : Type'} (_60259 : A -> Prop) (P : type686 A) (_60260 : A -> Prop) : ((term163 A P _60259 _60260) = (term180 A _60259 P _60260)) = True.
Proof. exact (TRANS (@lem4870054 A _60259 P _60260) (@lem4870058 A _60259 P _60260)). Qed.
Lemma lem4870060 {A : Type'} (_60259 : A -> Prop) (P : type686 A) (_60260 : A -> Prop) : True = ((term163 A P _60259 _60260) = (term180 A _60259 P _60260)).
Proof. exact (SYM (@lem4870059 A _60259 P _60260)). Qed.
Lemma lem4870061 {A : Type'} (_60259 : A -> Prop) (P : type686 A) (_60260 : A -> Prop) : (term163 A P _60259 _60260) = (term180 A _60259 P _60260).
Proof. exact (EQ_MP (@lem4870060 A _60259 P _60260) (@lem0)). Qed.
Lemma lem4870062 {A : Type'} (_60259 : A -> Prop) (_60260 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term180 A _60259 P _60260.
Proof. exact (EQ_MP (@lem4870061 A _60259 P _60260) (@lem4869905 A _60259 _60260 P s t h1)). Qed.
Lemma lem4870064 (b : Prop) (a : Prop) : (a \/ b) = (term169 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4870065 {A : Type'} (P : type686 A) (_60259 : A -> Prop) (_60260 : A -> Prop) : (term180 A _60259 P _60260) = (term183 A P _60259 _60260).
Proof. exact (@lem4870064 (term150 A _60259 P _60260) (term137 A P _60259 _60260)). Qed.
Lemma lem4870067 (a : Prop) (b : Prop) : (term184 a b) = (term185 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4870068 {A : Type'} (_60259 : A -> Prop) (P : type686 A) (_60260 : A -> Prop) : (term186 A _60259 P _60260) = (term187 A _60259 P _60260).
Proof. exact (@lem4870067 (term147 A P _60259) (term147 A P _60260)). Qed.
Lemma lem4870070 (a : Prop) : (term171 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4870071 {A : Type'} (P : type686 A) (_60259 : A -> Prop) : (term188 A P _60259) = (term124 A P _60259).
Proof. exact (@lem4870070 (term124 A P _60259)). Qed.
Lemma lem4870072 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4870073 {A : Type'} (P : type686 A) (_60259 : A -> Prop) : (term189 A P _60259) = (term190 A P _60259).
Proof. exact (MK_COMB (@lem4870072) (@lem4870071 A P _60259)). Qed.
Lemma lem4870075 (a : Prop) : (term171 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4870076 {A : Type'} (P : type686 A) (_60260 : A -> Prop) : (term188 A P _60260) = (term124 A P _60260).
Proof. exact (@lem4870075 (term124 A P _60260)). Qed.
Lemma lem4870077 {A : Type'} (_60259 : A -> Prop) (P : type686 A) (_60260 : A -> Prop) : (term187 A _60259 P _60260) = (term191 A _60259 P _60260).
Proof. exact (MK_COMB (@lem4870073 A P _60259) (@lem4870076 A P _60260)). Qed.
Lemma lem4870078 {A : Type'} (_60259 : A -> Prop) (P : type686 A) (_60260 : A -> Prop) : (term186 A _60259 P _60260) = (term191 A _60259 P _60260).
Proof. exact (TRANS (@lem4870068 A _60259 P _60260) (@lem4870077 A _60259 P _60260)). Qed.
Lemma lem4870079 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4870080 {A : Type'} (_60259 : A -> Prop) (P : type686 A) (_60260 : A -> Prop) : (term192 A _60259 P _60260) = (term193 A _60259 P _60260).
Proof. exact (MK_COMB (@lem4870079) (@lem4870078 A _60259 P _60260)). Qed.
Lemma lem4870081 {A : Type'} (P : type686 A) (_60259 : A -> Prop) (_60260 : A -> Prop) : (term137 A P _60259 _60260) = (term137 A P _60259 _60260).
Proof. exact (eq_refl (term137 A P _60259 _60260)). Qed.
Lemma lem4870082 {A : Type'} (P : type686 A) (_60259 : A -> Prop) (_60260 : A -> Prop) : (term183 A P _60259 _60260) = (term194 A P _60259 _60260).
Proof. exact (MK_COMB (@lem4870080 A _60259 P _60260) (@lem4870081 A P _60259 _60260)). Qed.
Lemma lem4870083 {A : Type'} (P : type686 A) (_60259 : A -> Prop) (_60260 : A -> Prop) : (term180 A _60259 P _60260) = (term194 A P _60259 _60260).
Proof. exact (TRANS (@lem4870065 A P _60259 _60260) (@lem4870082 A P _60259 _60260)). Qed.
Lemma lem4870085 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term24 A) (h2 : term111 A P s t) : term191 A s P t.
Proof. exact (conj (@lem4869971 A P s t h1 h2) (@lem4869990 A P s t h1 h2)). Qed.
Lemma lem4870087 {A : Type'} (_60259 : A -> Prop) (_60260 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term194 A P _60259 _60260.
Proof. exact (EQ_MP (@lem4870083 A P _60259 _60260) (@lem4870062 A _60259 _60260 P s t h1)). Qed.
Lemma lem4870088 {A : Type'} (_60259 : A -> Prop) (_60260 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term194 A P _60259 _60260.
Proof. exact (@lem4870087 A _60259 _60260 P s t h1). Qed.
Lemma lem4870089 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term194 A P s t.
Proof. exact (@lem4870088 A s t P s t h1). Qed.
Lemma lem4870092 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term24 A) (h2 : term111 A P s t) : term137 A P s t.
Proof. exact (@lem4870089 A P s t h2 (@lem4870085 A P s t h1 h2)). Qed.
Lemma lem4870093 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term24 A) (h2 : term111 A P s t) : term195 A P s t.
Proof. exact (fun h0 : term139 A P s t => @lem4870092 A P s t h1 h2). Qed.
Lemma lem4870095 (p : Prop) : (term165 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4870096 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term195 A P s t) = (term137 A P s t).
Proof. exact (@lem4870095 (term137 A P s t)). Qed.
Lemma lem4870097 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term24 A) (h2 : term111 A P s t) : term137 A P s t.
Proof. exact (EQ_MP (@lem4870096 A P s t) (@lem4870093 A P s t h1 h2)). Qed.
Lemma lem4870100 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4870102 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term139 A P s t) = (term196 A P s t).
Proof. exact (@lem4870100 (term137 A P s t)). Qed.
Lemma lem4870105 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term196 A P s t.
Proof. exact (EQ_MP (@lem4870102 A P s t) (@lem4869907 A P s t h1)). Qed.
Lemma lem4870108 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term24 A) (h2 : term111 A P s t) : False.
Proof. exact (@lem4870105 A P s t h2 (@lem4870097 A P s t h1 h2)). Qed.
Lemma lem4870109 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term24 A) (h2 : term111 A P s t) : term197.
Proof. exact (fun h0 : ~ False => @lem4870108 A P s t h1 h2). Qed.
Lemma lem4870111 (p : Prop) : (term165 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4870112 : term197 = False.
Proof. exact (@lem4870111 False). Qed.
Lemma lem4870113 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term24 A) (h2 : term111 A P s t) : False.
Proof. exact (EQ_MP (@lem4870112) (@lem4870109 A P s t h1 h2)). Qed.
Lemma lem4870114 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term24 A) (h2 : term114 A P s) : False.
Proof. exact (ex_elim (@lem4869592 A P s h2) (fun t : A -> Prop => fun h0 : term113 A P s t => @lem4870113 A P s t h1 h0)). Qed.
Lemma lem4870115 {A : Type'} (P : type686 A) (h1 : term24 A) (h2 : term23 A P) : False.
Proof. exact (ex_elim (@lem4869521 A P h2) (fun s : A -> Prop => fun h0 : term115 A P s => @lem4870114 A P s h1 h0)). Qed.
Lemma lem4870116 {A : Type'} (P : type686 A) (h1 : term23 A P) : term29 A.
Proof. exact (fun h0 : term24 A => @lem4870115 A P h0 h1). Qed.
Lemma lem4870117 {A : Type'} : (term29 A) = (term30 A).
Proof. exact (@lem69 (term24 A)). Qed.
Lemma lem4870118 {A : Type'} (P : type686 A) (h1 : term23 A P) : term30 A.
Proof. exact (EQ_MP (@lem4870117 A) (@lem4870116 A P h1)). Qed.
Lemma lem4870119 {A : Type'} (P : type686 A) : term32 A P.
Proof. exact (fun h0 : term23 A P => @lem4870118 A P h0). Qed.
Lemma lem4870124 {A : Type'} : term36 A.
Proof. exact (fun P : type686 A => @lem4870119 A P). Qed.
Lemma lem4870125 {A : Type'} : term35 A.
Proof. exact (EQ_MP (@lem4869312 A) (@lem4870124 A)). Qed.
Lemma lem4870126 {A : Type'} (P : type686 A) : term198 A P.
Proof. exact (@lem4870125 A P). Qed.
Lemma lem4870127 {A : Type'} (P : type686 A) : (term198 A P) = (term25 A P).
Proof. exact (eq_refl (term198 A P)). Qed.
Lemma lem4870128 {A : Type'} (P : type686 A) : term25 A P.
Proof. exact (EQ_MP (@lem4870127 A P) (@lem4870126 A P)). Qed.
Lemma lem4870130 {A : Type'} (P : type686 A) : term25 A P.
Proof. exact (@lem4869138 A P (@lem4870128 A P)). Qed.
Lemma lem4870131 {A : Type'} (P : type686 A) (h1 : term23 A P) : term29 A.
Proof. exact (@lem4870130 A P (@lem4869120 A P h1)). Qed.
Lemma lem4870132 {A : Type'} (P : type686 A) (h1 : term23 A P) : False.
Proof. exact (@lem4870131 A P h1 (@lem4869121 A)). Qed.
Lemma lem4870133 {A : Type'} (P : type686 A) (h1 : term23 A P) : (term23 A P) = False.
Proof. exact (prop_ext (fun h2 : term23 A P => @lem4870132 A P h1) (fun h2 : False => @lem4869120 A P h1)). Qed.
Lemma lem4870134 {A : Type'} (P : type686 A) (h1 : term23 A P) : False.
Proof. exact (EQ_MP (@lem4870133 A P h1) (@lem4869120 A P h1)). Qed.
Lemma lem4870135 {A : Type'} (P : type686 A) : term22 A P.
Proof. exact (fun h0 : term23 A P => @lem4870134 A P h0). Qed.
Lemma lem4870136 {A : Type'} (P : type686 A) : term21 A P.
Proof. exact (EQ_MP (@lem4869119 A P) (@lem4870135 A P)). Qed.
Lemma lem4870137 {A : Type'} (P : type686 A) (h1 : term45 A P) : term45 A P.
Proof. exact (h1). Qed.
Lemma lem4870139 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term12 A P Q).
Proof. exact (EQ_MP (@lem4869104 A P Q) (@lem4869103 A P Q)). Qed.
Lemma lem4870140 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term12 A P Q).
Proof. exact (@lem4870139 A P Q). Qed.
Lemma lem4870141 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (term199 A P).
Proof. exact (@lem4870140 A (@ARBITRARY A) P). Qed.
Lemma lem4870142 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4870143 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@ARBITRARY A) P s) = (term200 A P s).
Proof. exact (MK_COMB (@lem4870141 A P) (@lem4870142 A s)). Qed.
Lemma lem4870144 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4870145 {A : Type'} (P : type686 A) (s : A -> Prop) : (term201 A P s) = (term202 A P s).
Proof. exact (MK_COMB (@lem4870144) (@lem4870143 A P s)). Qed.
Lemma lem4870147 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term12 A P Q).
Proof. exact (EQ_MP (@lem4869104 A P Q) (@lem4869103 A P Q)). Qed.
Lemma lem4870148 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term12 A P Q).
Proof. exact (@lem4870147 A P Q). Qed.
Lemma lem4870149 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (term199 A P).
Proof. exact (@lem4870148 A (@ARBITRARY A) P). Qed.
Lemma lem4870150 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4870151 {A : Type'} (P : type686 A) (t : A -> Prop) : (@UNION_OF A (@ARBITRARY A) P t) = (term200 A P t).
Proof. exact (MK_COMB (@lem4870149 A P) (@lem4870150 A t)). Qed.
Lemma lem4870152 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term59 A s P t) = (term203 A s P t).
Proof. exact (MK_COMB (@lem4870145 A P s) (@lem4870151 A P t)). Qed.
Lemma lem4870153 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4870154 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term204 A s P t) = (term205 A s P t).
Proof. exact (MK_COMB (@lem4870153) (@lem4870152 A s P t)). Qed.
Lemma lem4870155 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term54 A P s t) = (term54 A P s t).
Proof. exact (eq_refl (term54 A P s t)). Qed.
Lemma lem4870156 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term46 A P s t) = (term206 A P s t).
Proof. exact (MK_COMB (@lem4870154 A s P t) (@lem4870155 A P s t)). Qed.
Lemma lem4870157 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term206 A P s t) = (term46 A P s t).
Proof. exact (SYM (@lem4870156 A P s t)). Qed.
Lemma lem4870163 {A B : Type'} (f : A -> B) (y : A) : (term207 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4870164 {A : Type'} (f : type686 A) (y : A -> Prop) : (term208 A f y) = (f y).
Proof. exact (@lem4870163 (A -> Prop) Prop f y). Qed.
Lemma lem4870165 {A : Type'} (P : type686 A) (s : A -> Prop) : (term209 A P s) = (term200 A P s).
Proof. exact (@lem4870164 A (term199 A P) s). Qed.
Lemma lem4870166 {A : Type'} (P : type686 A) (s : A -> Prop) : (term200 A P s) = (term210 A P s).
Proof. exact (eq_refl (term200 A P s)). Qed.
Lemma lem4870167 {A : Type'} (P : type686 A) : (term211 A P) = (term199 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4870166 A P s)). Qed.
Lemma lem4870168 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4870169 {A : Type'} (P : type686 A) (s : A -> Prop) : (term209 A P s) = (term200 A P s).
Proof. exact (MK_COMB (@lem4870167 A P) (@lem4870168 A s)). Qed.
Lemma lem4870170 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4870171 {A : Type'} (P : type686 A) (s : A -> Prop) : (term212 A P s) = (term213 A P s).
Proof. exact (MK_COMB (@lem4870170) (@lem4870169 A P s)). Qed.
Lemma lem4870172 {A : Type'} (P : type686 A) (s : A -> Prop) : (term200 A P s) = (term210 A P s).
Proof. exact (eq_refl (term200 A P s)). Qed.
Lemma lem4870173 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term209 A P s) = (term200 A P s)) = ((term200 A P s) = (term210 A P s)).
Proof. exact (MK_COMB (@lem4870171 A P s) (@lem4870172 A P s)). Qed.
Lemma lem4870174 {A : Type'} (P : type686 A) (s : A -> Prop) : (term200 A P s) = (term210 A P s).
Proof. exact (EQ_MP (@lem4870173 A P s) (@lem4870165 A P s)). Qed.
Lemma lem4870191 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4870192 {A : Type'} (P : type686 A) (s : A -> Prop) : (term202 A P s) = (term214 A P s).
Proof. exact (MK_COMB (@lem4870191) (@lem4870174 A P s)). Qed.
Lemma lem4870194 {A B : Type'} (f : A -> B) (y : A) : (term207 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4870195 {A : Type'} (f : type686 A) (y : A -> Prop) : (term208 A f y) = (f y).
Proof. exact (@lem4870194 (A -> Prop) Prop f y). Qed.
Lemma lem4870196 {A : Type'} (P : type686 A) (t : A -> Prop) : (term209 A P t) = (term200 A P t).
Proof. exact (@lem4870195 A (term199 A P) t). Qed.
Lemma lem4870197 {A : Type'} (P : type686 A) (s : A -> Prop) : (term200 A P s) = (term210 A P s).
Proof. exact (eq_refl (term200 A P s)). Qed.
Lemma lem4870198 {A : Type'} (P : type686 A) : (term211 A P) = (term199 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4870197 A P s)). Qed.
Lemma lem4870199 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4870200 {A : Type'} (P : type686 A) (t : A -> Prop) : (term209 A P t) = (term200 A P t).
Proof. exact (MK_COMB (@lem4870198 A P) (@lem4870199 A t)). Qed.
Lemma lem4870201 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4870202 {A : Type'} (P : type686 A) (t : A -> Prop) : (term212 A P t) = (term213 A P t).
Proof. exact (MK_COMB (@lem4870201) (@lem4870200 A P t)). Qed.
Lemma lem4870203 {A : Type'} (P : type686 A) (t : A -> Prop) : (term200 A P t) = (term210 A P t).
Proof. exact (eq_refl (term200 A P t)). Qed.
Lemma lem4870204 {A : Type'} (P : type686 A) (t : A -> Prop) : ((term209 A P t) = (term200 A P t)) = ((term200 A P t) = (term210 A P t)).
Proof. exact (MK_COMB (@lem4870202 A P t) (@lem4870203 A P t)). Qed.
Lemma lem4870205 {A : Type'} (P : type686 A) (t : A -> Prop) : (term200 A P t) = (term210 A P t).
Proof. exact (EQ_MP (@lem4870204 A P t) (@lem4870196 A P t)). Qed.
Lemma lem4870222 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term203 A s P t) = (term215 A s P t).
Proof. exact (MK_COMB (@lem4870192 A P s) (@lem4870205 A P t)). Qed.
Lemma lem4870225 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4870226 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term205 A s P t) = (term216 A s P t).
Proof. exact (MK_COMB (@lem4870225) (@lem4870222 A s P t)). Qed.
Lemma lem4870227 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term54 A P s t) = (term54 A P s t).
Proof. exact (eq_refl (term54 A P s t)). Qed.
Lemma lem4870228 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term206 A P s t) = (term217 A P s t).
Proof. exact (MK_COMB (@lem4870226 A s P t) (@lem4870227 A P s t)). Qed.
Lemma lem4870231 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term217 A P s t) = (term206 A P s t).
Proof. exact (SYM (@lem4870228 A P s t)). Qed.
Lemma lem4870232 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) (h1 : term215 A s P t) : term215 A s P t.
Proof. exact (h1). Qed.
Lemma lem4870242 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : (@UNIONS A u) = s.
Proof. exact (h1). Qed.
Lemma lem4870243 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : s = (@UNIONS A u).
Proof. exact (SYM (@lem4870242 A u s h1)). Qed.
Lemma lem4870244 {A : Type'} (s : A -> Prop) (u : type686 A) (h1 : s = (@UNIONS A u)) : s = (@UNIONS A u).
Proof. exact (h1). Qed.
Lemma lem4870245 {A : Type'} (s : A -> Prop) (u : type686 A) (h1 : s = (@UNIONS A u)) : (@UNIONS A u) = s.
Proof. exact (SYM (@lem4870244 A s u h1)). Qed.
Lemma lem4870246 {A : Type'} (s : A -> Prop) (u : type686 A) : ((@UNIONS A u) = s) = (s = (@UNIONS A u)).
Proof. exact (prop_ext (fun h1 : (@UNIONS A u) = s => @lem4870243 A u s h1) (fun h1 : s = (@UNIONS A u) => @lem4870245 A s u h1)). Qed.
Lemma lem4870247 {A : Type'} (u : type686 A) (P : type686 A) : (term218 A u P) = (term218 A u P).
Proof. exact (eq_refl (term218 A u P)). Qed.
Lemma lem4870248 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) : (term219 A P u s) = (term220 A P s u).
Proof. exact (MK_COMB (@lem4870247 A u P) (@lem4870246 A s u)). Qed.
Lemma lem4870249 {A : Type'} (u : type686 A) : (term221 A u) = (term221 A u).
Proof. exact (eq_refl (term221 A u)). Qed.
Lemma lem4870250 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) : (term222 A P u s) = (term223 A P s u).
Proof. exact (MK_COMB (@lem4870249 A u) (@lem4870248 A P s u)). Qed.
Lemma lem4870251 {A : Type'} (P : type686 A) (s : A -> Prop) : (term224 A P s) = (term225 A P s).
Proof. exact (fun_ext (fun u : type686 A => @lem4870250 A P s u)). Qed.
Lemma lem4870252 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4870253 {A : Type'} (P : type686 A) (s : A -> Prop) : (term210 A P s) = (term226 A P s).
Proof. exact (MK_COMB (@lem4870252 A) (@lem4870251 A P s)). Qed.
Lemma lem4870254 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4870255 {A : Type'} (P : type686 A) (s : A -> Prop) : (term214 A P s) = (term227 A P s).
Proof. exact (MK_COMB (@lem4870254) (@lem4870253 A P s)). Qed.
Lemma lem4870264 {A : Type'} (u : type686 A) (t : A -> Prop) (h1 : (@UNIONS A u) = t) : (@UNIONS A u) = t.
Proof. exact (h1). Qed.
Lemma lem4870265 {A : Type'} (u : type686 A) (t : A -> Prop) (h1 : (@UNIONS A u) = t) : t = (@UNIONS A u).
Proof. exact (SYM (@lem4870264 A u t h1)). Qed.
Lemma lem4870266 {A : Type'} (t : A -> Prop) (u : type686 A) (h1 : t = (@UNIONS A u)) : t = (@UNIONS A u).
Proof. exact (h1). Qed.
Lemma lem4870267 {A : Type'} (t : A -> Prop) (u : type686 A) (h1 : t = (@UNIONS A u)) : (@UNIONS A u) = t.
Proof. exact (SYM (@lem4870266 A t u h1)). Qed.
Lemma lem4870268 {A : Type'} (t : A -> Prop) (u : type686 A) : ((@UNIONS A u) = t) = (t = (@UNIONS A u)).
Proof. exact (prop_ext (fun h1 : (@UNIONS A u) = t => @lem4870265 A u t h1) (fun h1 : t = (@UNIONS A u) => @lem4870267 A t u h1)). Qed.
Lemma lem4870269 {A : Type'} (u : type686 A) (P : type686 A) : (term218 A u P) = (term218 A u P).
Proof. exact (eq_refl (term218 A u P)). Qed.
Lemma lem4870270 {A : Type'} (P : type686 A) (t : A -> Prop) (u : type686 A) : (term219 A P u t) = (term220 A P t u).
Proof. exact (MK_COMB (@lem4870269 A u P) (@lem4870268 A t u)). Qed.
Lemma lem4870271 {A : Type'} (u : type686 A) : (term221 A u) = (term221 A u).
Proof. exact (eq_refl (term221 A u)). Qed.
Lemma lem4870272 {A : Type'} (P : type686 A) (t : A -> Prop) (u : type686 A) : (term222 A P u t) = (term223 A P t u).
Proof. exact (MK_COMB (@lem4870271 A u) (@lem4870270 A P t u)). Qed.
Lemma lem4870273 {A : Type'} (P : type686 A) (t : A -> Prop) : (term224 A P t) = (term225 A P t).
Proof. exact (fun_ext (fun u : type686 A => @lem4870272 A P t u)). Qed.
Lemma lem4870274 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4870275 {A : Type'} (P : type686 A) (t : A -> Prop) : (term210 A P t) = (term226 A P t).
Proof. exact (MK_COMB (@lem4870274 A) (@lem4870273 A P t)). Qed.
Lemma lem4870276 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term215 A s P t) = (term228 A s P t).
Proof. exact (MK_COMB (@lem4870255 A P s) (@lem4870275 A P t)). Qed.
Lemma lem4870277 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) (h1 : term215 A s P t) : term228 A s P t.
Proof. exact (EQ_MP (@lem4870276 A s P t) (@lem4870232 A s P t h1)). Qed.
Lemma lem4870278 {A : Type'} (P : type686 A) (t : A -> Prop) (h1 : term226 A P t) : term226 A P t.
Proof. exact (h1). Qed.
Lemma lem4870279 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term226 A P s) : term226 A P s.
Proof. exact (h1). Qed.
Lemma lem4870280 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term223 A P s u) : term223 A P s u.
Proof. exact (h1). Qed.
Lemma lem4870281 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term220 A P s u) : term220 A P s u.
Proof. exact (h1). Qed.
Lemma lem4870283 {A : Type'} (s : A -> Prop) (u : type686 A) (h1 : s = (@UNIONS A u)) : s = (@UNIONS A u).
Proof. exact (h1). Qed.
Lemma lem4870284 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term229 A u P) : term229 A u P.
Proof. exact (h1). Qed.
Lemma lem4870285 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : term223 A P t u') : term223 A P t u'.
Proof. exact (h1). Qed.
Lemma lem4870286 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : term220 A P t u') : term220 A P t u'.
Proof. exact (h1). Qed.
Lemma lem4870288 {A : Type'} (t : A -> Prop) (u' : type686 A) (h1 : t = (@UNIONS A u')) : t = (@UNIONS A u').
Proof. exact (h1). Qed.
Lemma lem4870289 {A : Type'} (u' : type686 A) (P : type686 A) (h1 : term229 A u' P) : term229 A u' P.
Proof. exact (h1). Qed.
Lemma lem4870290 {_87026 : Type'} : term230 _87026.
Proof. exact (proj2 (@lem3341279 Prop _87026)). Qed.
Lemma lem4870291 {_87026 : Type'} (s : type686 _87026) : term231 _87026 s.
Proof. exact (@lem4870290 _87026 s). Qed.
Lemma lem4870292 {_87026 : Type'} (s : type686 _87026) : (term231 _87026 s) = (term232 _87026 s).
Proof. exact (eq_refl (term231 _87026 s)). Qed.
Lemma lem4870293 {_87026 : Type'} (s : type686 _87026) : term232 _87026 s.
Proof. exact (EQ_MP (@lem4870292 _87026 s) (@lem4870291 _87026 s)). Qed.
Lemma lem4870294 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : term233 _87026 s t.
Proof. exact (@lem4870293 _87026 s t). Qed.
Lemma lem4870295 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term233 _87026 s t) = ((term234 _87026 t s) = (term235 _87026 s t)).
Proof. exact (eq_refl (term233 _87026 s t)). Qed.
Lemma lem4870297 {_86990 : Type'} : term236 _86990.
Proof. exact (proj1 (@lem3341279 _86990 Prop)). Qed.
Lemma lem4870298 {_86990 : Type'} (s : type686 _86990) : term237 _86990 s.
Proof. exact (@lem4870297 _86990 s). Qed.
Lemma lem4870299 {_86990 : Type'} (s : type686 _86990) : (term237 _86990 s) = (term238 _86990 s).
Proof. exact (eq_refl (term237 _86990 s)). Qed.
Lemma lem4870300 {_86990 : Type'} (s : type686 _86990) : term238 _86990 s.
Proof. exact (EQ_MP (@lem4870299 _86990 s) (@lem4870298 _86990 s)). Qed.
Lemma lem4870301 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : term239 _86990 s t.
Proof. exact (@lem4870300 _86990 s t). Qed.
Lemma lem4870302 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term239 _86990 s t) = ((term240 _86990 s t) = (term241 _86990 s t)).
Proof. exact (eq_refl (term239 _86990 s t)). Qed.
Lemma lem4870327 {A : Type'} (s : A -> Prop) (u : type686 A) (h1 : s = (@UNIONS A u)) : s = (@UNIONS A u).
Proof. exact (h1). Qed.
Lemma lem4870328 {A : Type'} : (@INTER A) = (@INTER A).
Proof. exact (eq_refl (@INTER A)). Qed.
Lemma lem4870329 {A : Type'} (s : A -> Prop) (u : type686 A) (h1 : s = (@UNIONS A u)) : (@INTER A s) = (term242 A u).
Proof. exact (MK_COMB (@lem4870328 A) (@lem4870327 A s u h1)). Qed.
Lemma lem4870331 {A : Type'} (t : A -> Prop) (u' : type686 A) (h1 : t = (@UNIONS A u')) : t = (@UNIONS A u').
Proof. exact (h1). Qed.
Lemma lem4870332 {A : Type'} (s : A -> Prop) (u : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : s = (@UNIONS A u)) (h2 : t = (@UNIONS A u')) : (@INTER A s t) = (term243 A u u').
Proof. exact (MK_COMB (@lem4870329 A s u h1) (@lem4870331 A t u' h2)). Qed.
Lemma lem4870334 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term240 _86990 s t) = (term241 _86990 s t).
Proof. exact (EQ_MP (@lem4870302 _86990 s t) (@lem4870301 _86990 s t)). Qed.
Lemma lem4870335 {A : Type'} (s : type686 A) (t : A -> Prop) : (term240 A s t) = (term241 A s t).
Proof. exact (@lem4870334 A s t). Qed.
Lemma lem4870336 {A : Type'} (u : type686 A) (u' : type686 A) : (term243 A u u') = (term244 A u u').
Proof. exact (@lem4870335 A u (@UNIONS A u')). Qed.
Lemma lem4870342 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term234 _87026 t s) = (term235 _87026 s t).
Proof. exact (EQ_MP (@lem4870295 _87026 s t) (@lem4870294 _87026 s t)). Qed.
Lemma lem4870343 {A : Type'} (s : type686 A) (t : A -> Prop) : (term234 A t s) = (term235 A s t).
Proof. exact (@lem4870342 A s t). Qed.
Lemma lem4870344 {A : Type'} (u' : type686 A) (x : A -> Prop) : (term234 A x u') = (term235 A u' x).
Proof. exact (@lem4870343 A u' x). Qed.
Lemma lem4870349 {A : Type'} (GEN_PVAR_21 : A -> Prop) (x : A -> Prop) (u : type686 A) : (term245 A GEN_PVAR_21 x u) = (term245 A GEN_PVAR_21 x u).
Proof. exact (eq_refl (term245 A GEN_PVAR_21 x u)). Qed.
Lemma lem4870350 {A : Type'} (GEN_PVAR_21 : A -> Prop) (u : type686 A) (u' : type686 A) (x : A -> Prop) : (term246 A GEN_PVAR_21 u x u') = (term247 A GEN_PVAR_21 u u' x).
Proof. exact (MK_COMB (@lem4870349 A GEN_PVAR_21 x u) (@lem4870344 A u' x)). Qed.
Lemma lem4870351 {A : Type'} (GEN_PVAR_21 : A -> Prop) (u : type686 A) (u' : type686 A) : (term248 A GEN_PVAR_21 u u') = (term249 A GEN_PVAR_21 u u').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4870350 A GEN_PVAR_21 u u' x)). Qed.
Lemma lem4870352 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4870353 {A : Type'} (GEN_PVAR_21 : A -> Prop) (u : type686 A) (u' : type686 A) : (term250 A GEN_PVAR_21 u u') = (term251 A GEN_PVAR_21 u u').
Proof. exact (MK_COMB (@lem4870352 A) (@lem4870351 A GEN_PVAR_21 u u')). Qed.
Lemma lem4870358 {A : Type'} (u : type686 A) (u' : type686 A) : (term252 A u u') = (term253 A u u').
Proof. exact (fun_ext (fun GEN_PVAR_21 : A -> Prop => @lem4870353 A GEN_PVAR_21 u u')). Qed.
Lemma lem4870359 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4870360 {A : Type'} (u : type686 A) (u' : type686 A) : (term254 A u u') = (term255 A u u').
Proof. exact (MK_COMB (@lem4870359 A) (@lem4870358 A u u')). Qed.
Lemma lem4870361 {A : Type'} : (@UNIONS A) = (@UNIONS A).
Proof. exact (eq_refl (@UNIONS A)). Qed.
Lemma lem4870362 {A : Type'} (u : type686 A) (u' : type686 A) : (term244 A u u') = (term256 A u u').
Proof. exact (MK_COMB (@lem4870361 A) (@lem4870360 A u u')). Qed.
Lemma lem4870363 {A : Type'} (u : type686 A) (u' : type686 A) : (term243 A u u') = (term256 A u u').
Proof. exact (TRANS (@lem4870336 A u u') (@lem4870362 A u u')). Qed.
Lemma lem4870364 {A : Type'} (s : A -> Prop) (u : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : s = (@UNIONS A u)) (h2 : t = (@UNIONS A u')) : (@INTER A s t) = (term256 A u u').
Proof. exact (TRANS (@lem4870332 A s u t u' h1 h2) (@lem4870363 A u u')). Qed.
Lemma lem4870365 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (@UNION_OF A (@ARBITRARY A) P).
Proof. exact (eq_refl (@UNION_OF A (@ARBITRARY A) P)). Qed.
Lemma lem4870366 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : s = (@UNIONS A u)) (h2 : t = (@UNIONS A u')) : (term54 A P s t) = (term257 A P u u').
Proof. exact (MK_COMB (@lem4870365 A P) (@lem4870364 A s u t u' h1 h2)). Qed.
Lemma lem4870367 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : s = (@UNIONS A u)) (h2 : t = (@UNIONS A u')) : (term257 A P u u') = (term54 A P s t).
Proof. exact (SYM (@lem4870366 A P s u t u' h1 h2)). Qed.
Lemma lem4870369 {A : Type'} (P : type686 A) (u : type686 A) : term4 A P u.
Proof. exact (EQ_MP (@lem4869098 A P u) (@lem4869097 A P u)). Qed.
Lemma lem4870370 {A : Type'} (P : type686 A) (u : type686 A) : term4 A P u.
Proof. exact (@lem4870369 A P u). Qed.
Lemma lem4870371 {A : Type'} (P : type686 A) (u : type686 A) (u' : type686 A) : term258 A P u u'.
Proof. exact (@lem4870370 A P (term255 A u u')). Qed.
Lemma lem4870372 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term259 _87967 _87968 P f.
Proof. exact (@lem3386920 _87967 _87968 P f). Qed.
Lemma lem4870373 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term259 _87967 _87968 P f) = (term260 _87967 _87968 P f).
Proof. exact (eq_refl (term259 _87967 _87968 P f)). Qed.
Lemma lem4870374 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term260 _87967 _87968 P f.
Proof. exact (EQ_MP (@lem4870373 _87967 _87968 P f) (@lem4870372 _87967 _87968 P f)). Qed.
Lemma lem4870375 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (s : _87968 -> Prop) : term261 _87967 _87968 P f s.
Proof. exact (@lem4870374 _87967 _87968 P f s). Qed.
Lemma lem4870376 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term261 _87967 _87968 P f s) = ((term262 _87967 _87968 f s P) = (term263 _87967 _87968 s P f)).
Proof. exact (eq_refl (term261 _87967 _87968 P f s)). Qed.
Lemma lem4870381 {_88128 _88132 : Type'} (f : _88128 -> _88132) : term264 _88128 _88132 f.
Proof. exact (@lem3393993 _88128 _88132 f). Qed.
Lemma lem4870382 {_88128 _88132 : Type'} (f : _88128 -> _88132) : (term264 _88128 _88132 f) = (term265 _88128 _88132 f).
Proof. exact (eq_refl (term264 _88128 _88132 f)). Qed.
Lemma lem4870383 {_88128 _88132 : Type'} (f : _88128 -> _88132) : term265 _88128 _88132 f.
Proof. exact (EQ_MP (@lem4870382 _88128 _88132 f) (@lem4870381 _88128 _88132 f)). Qed.
Lemma lem4870384 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : term266 _88128 _88132 f s.
Proof. exact (@lem4870383 _88128 _88132 f s). Qed.
Lemma lem4870385 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term266 _88128 _88132 f s) = ((term267 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s)).
Proof. exact (eq_refl (term266 _88128 _88132 f s)). Qed.
Lemma lem4870534 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term268 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4870535 (p : Prop) (q : Prop) (p' : Prop) : term269 p q p'.
Proof. exact (fun q' : Prop => @lem4870534 p q p' q'). Qed.
Lemma lem4870536 (p : Prop) (q : Prop) : term270 p q.
Proof. exact (fun p' : Prop => @lem4870535 p q p'). Qed.
Lemma lem4870537 {A : Type'} (u : type686 A) (u' : type686 A) (P : type686 A) (_60261 : A -> Prop) : term271 A u u' P _60261.
Proof. exact (@lem4870536 (term272 A _60261 u u') (@UNION_OF A (@ARBITRARY A) P _60261)). Qed.
Lemma lem4870538 {A : Type'} (u : type686 A) (u' : type686 A) (P : type686 A) (_60261 : A -> Prop) (p' : Prop) : term273 A u u' P _60261 p'.
Proof. exact (@lem4870537 A u u' P _60261 p'). Qed.
Lemma lem4870539 {A : Type'} (u : type686 A) (u' : type686 A) (P : type686 A) (_60261 : A -> Prop) (p' : Prop) : (term273 A u u' P _60261 p') = (term274 A u u' P _60261 p').
Proof. exact (eq_refl (term273 A u u' P _60261 p')). Qed.
Lemma lem4870540 {A : Type'} (u : type686 A) (u' : type686 A) (P : type686 A) (_60261 : A -> Prop) (p' : Prop) : term274 A u u' P _60261 p'.
Proof. exact (EQ_MP (@lem4870539 A u u' P _60261 p') (@lem4870538 A u u' P _60261 p')). Qed.
Lemma lem4870541 {A : Type'} (u : type686 A) (u' : type686 A) (P : type686 A) (_60261 : A -> Prop) (p' : Prop) (q' : Prop) : term275 A u u' P _60261 p' q'.
Proof. exact (@lem4870540 A u u' P _60261 p' q'). Qed.
Lemma lem4870542 {A : Type'} (u : type686 A) (u' : type686 A) (P : type686 A) (_60261 : A -> Prop) (p' : Prop) (q' : Prop) : (term275 A u u' P _60261 p' q') = (term276 A u u' P _60261 p' q').
Proof. exact (eq_refl (term275 A u u' P _60261 p' q')). Qed.
Lemma lem4870543 {A : Type'} (u : type686 A) (u' : type686 A) (P : type686 A) (_60261 : A -> Prop) (p' : Prop) (q' : Prop) : term276 A u u' P _60261 p' q'.
Proof. exact (EQ_MP (@lem4870542 A u u' P _60261 p' q') (@lem4870541 A u u' P _60261 p' q')). Qed.
Lemma lem4870545 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term267 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s).
Proof. exact (EQ_MP (@lem4870385 _88128 _88132 f s) (@lem4870384 _88128 _88132 f s)). Qed.
Lemma lem4870546 {A : Type'} (f : type672 A) (s : type686 A) : (term277 A s f) = (@IMAGE (A -> Prop) (A -> Prop) f s).
Proof. exact (@lem4870545 (A -> Prop) (A -> Prop) f s). Qed.
Lemma lem4870547 {A : Type'} (u' : type686 A) (u : type686 A) : (term278 A u u') = (term279 A u' u).
Proof. exact (@lem4870546 A (term280 A u') u). Qed.
Lemma lem4870548 {A : Type'} (u' : type686 A) (x : A -> Prop) : (term281 A u' x) = (term235 A u' x).
Proof. exact (eq_refl (term281 A u' x)). Qed.
Lemma lem4870549 {A : Type'} (GEN_PVAR_21 : A -> Prop) (x : A -> Prop) (u : type686 A) : (term245 A GEN_PVAR_21 x u) = (term245 A GEN_PVAR_21 x u).
Proof. exact (eq_refl (term245 A GEN_PVAR_21 x u)). Qed.
Lemma lem4870550 {A : Type'} (GEN_PVAR_21 : A -> Prop) (u : type686 A) (u' : type686 A) (x : A -> Prop) : (term282 A GEN_PVAR_21 u u' x) = (term247 A GEN_PVAR_21 u u' x).
Proof. exact (MK_COMB (@lem4870549 A GEN_PVAR_21 x u) (@lem4870548 A u' x)). Qed.
Lemma lem4870551 {A : Type'} (GEN_PVAR_21 : A -> Prop) (u : type686 A) (u' : type686 A) : (term283 A GEN_PVAR_21 u u') = (term249 A GEN_PVAR_21 u u').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4870550 A GEN_PVAR_21 u u' x)). Qed.
Lemma lem4870552 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4870553 {A : Type'} (GEN_PVAR_21 : A -> Prop) (u : type686 A) (u' : type686 A) : (term284 A GEN_PVAR_21 u u') = (term251 A GEN_PVAR_21 u u').
Proof. exact (MK_COMB (@lem4870552 A) (@lem4870551 A GEN_PVAR_21 u u')). Qed.
Lemma lem4870554 {A : Type'} (u : type686 A) (u' : type686 A) : (term285 A u u') = (term253 A u u').
Proof. exact (fun_ext (fun GEN_PVAR_21 : A -> Prop => @lem4870553 A GEN_PVAR_21 u u')). Qed.
Lemma lem4870555 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4870556 {A : Type'} (u : type686 A) (u' : type686 A) : (term278 A u u') = (term255 A u u').
Proof. exact (MK_COMB (@lem4870555 A) (@lem4870554 A u u')). Qed.
Lemma lem4870557 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4870558 {A : Type'} (u : type686 A) (u' : type686 A) : (term286 A u u') = (term287 A u u').
Proof. exact (MK_COMB (@lem4870557 A) (@lem4870556 A u u')). Qed.
Lemma lem4870559 {A : Type'} (u' : type686 A) (u : type686 A) : (term279 A u' u) = (term279 A u' u).
Proof. exact (eq_refl (term279 A u' u)). Qed.
Lemma lem4870560 {A : Type'} (u' : type686 A) (u : type686 A) : ((term278 A u u') = (term279 A u' u)) = ((term255 A u u') = (term279 A u' u)).
Proof. exact (MK_COMB (@lem4870558 A u u') (@lem4870559 A u' u)). Qed.
Lemma lem4870561 {A : Type'} (u' : type686 A) (u : type686 A) : (term255 A u u') = (term279 A u' u).
Proof. exact (EQ_MP (@lem4870560 A u' u) (@lem4870547 A u' u)). Qed.
Lemma lem4870563 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term267 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s).
Proof. exact (EQ_MP (@lem4870385 _88128 _88132 f s) (@lem4870384 _88128 _88132 f s)). Qed.
Lemma lem4870564 {A : Type'} (f : type672 A) (s : type686 A) : (term277 A s f) = (@IMAGE (A -> Prop) (A -> Prop) f s).
Proof. exact (@lem4870563 (A -> Prop) (A -> Prop) f s). Qed.
Lemma lem4870565 {A : Type'} (x : A -> Prop) (u' : type686 A) : (term288 A u' x) = (term289 A x u').
Proof. exact (@lem4870564 A (term290 A x) u'). Qed.
Lemma lem4870566 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term291 A x x') = (@INTER A x x').
Proof. exact (eq_refl (term291 A x x')). Qed.
Lemma lem4870567 {A : Type'} (GEN_PVAR_22 : A -> Prop) (x' : A -> Prop) (u' : type686 A) : (term245 A GEN_PVAR_22 x' u') = (term245 A GEN_PVAR_22 x' u').
Proof. exact (eq_refl (term245 A GEN_PVAR_22 x' u')). Qed.
Lemma lem4870568 {A : Type'} (GEN_PVAR_22 : A -> Prop) (u' : type686 A) (x : A -> Prop) (x' : A -> Prop) : (term292 A GEN_PVAR_22 u' x x') = (term293 A GEN_PVAR_22 u' x x').
Proof. exact (MK_COMB (@lem4870567 A GEN_PVAR_22 x' u') (@lem4870566 A x x')). Qed.
Lemma lem4870569 {A : Type'} (GEN_PVAR_22 : A -> Prop) (u' : type686 A) (x : A -> Prop) : (term294 A GEN_PVAR_22 u' x) = (term295 A GEN_PVAR_22 u' x).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4870568 A GEN_PVAR_22 u' x x')). Qed.
Lemma lem4870570 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4870571 {A : Type'} (GEN_PVAR_22 : A -> Prop) (u' : type686 A) (x : A -> Prop) : (term296 A GEN_PVAR_22 u' x) = (term297 A GEN_PVAR_22 u' x).
Proof. exact (MK_COMB (@lem4870570 A) (@lem4870569 A GEN_PVAR_22 u' x)). Qed.
Lemma lem4870572 {A : Type'} (u' : type686 A) (x : A -> Prop) : (term298 A u' x) = (term299 A u' x).
Proof. exact (fun_ext (fun GEN_PVAR_22 : A -> Prop => @lem4870571 A GEN_PVAR_22 u' x)). Qed.
Lemma lem4870573 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4870574 {A : Type'} (u' : type686 A) (x : A -> Prop) : (term288 A u' x) = (term300 A u' x).
Proof. exact (MK_COMB (@lem4870573 A) (@lem4870572 A u' x)). Qed.
Lemma lem4870575 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4870576 {A : Type'} (u' : type686 A) (x : A -> Prop) : (term301 A u' x) = (term302 A u' x).
Proof. exact (MK_COMB (@lem4870575 A) (@lem4870574 A u' x)). Qed.
Lemma lem4870577 {A : Type'} (x : A -> Prop) (u' : type686 A) : (term289 A x u') = (term289 A x u').
Proof. exact (eq_refl (term289 A x u')). Qed.
Lemma lem4870578 {A : Type'} (x : A -> Prop) (u' : type686 A) : ((term288 A u' x) = (term289 A x u')) = ((term300 A u' x) = (term289 A x u')).
Proof. exact (MK_COMB (@lem4870576 A u' x) (@lem4870577 A x u')). Qed.
Lemma lem4870579 {A : Type'} (x : A -> Prop) (u' : type686 A) : (term300 A u' x) = (term289 A x u').
Proof. exact (EQ_MP (@lem4870578 A x u') (@lem4870565 A x u')). Qed.
Lemma lem4870580 {A : Type'} : (@UNIONS A) = (@UNIONS A).
Proof. exact (eq_refl (@UNIONS A)). Qed.
Lemma lem4870581 {A : Type'} (x : A -> Prop) (u' : type686 A) : (term235 A u' x) = (term303 A x u').
Proof. exact (MK_COMB (@lem4870580 A) (@lem4870579 A x u')). Qed.
Lemma lem4870582 {A : Type'} (u' : type686 A) : (term280 A u') = (term304 A u').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4870581 A x u')). Qed.
Lemma lem4870583 {A : Type'} : (@IMAGE (A -> Prop) (A -> Prop)) = (@IMAGE (A -> Prop) (A -> Prop)).
Proof. exact (eq_refl (@IMAGE (A -> Prop) (A -> Prop))). Qed.
Lemma lem4870584 {A : Type'} (u' : type686 A) : (term305 A u') = (term306 A u').
Proof. exact (MK_COMB (@lem4870583 A) (@lem4870582 A u')). Qed.
Lemma lem4870585 {A : Type'} (u : type686 A) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem4870586 {A : Type'} (u' : type686 A) (u : type686 A) : (term279 A u' u) = (term307 A u' u).
Proof. exact (MK_COMB (@lem4870584 A u') (@lem4870585 A u)). Qed.
Lemma lem4870587 {A : Type'} (u' : type686 A) (u : type686 A) : (term255 A u u') = (term307 A u' u).
Proof. exact (TRANS (@lem4870561 A u' u) (@lem4870586 A u' u)). Qed.
Lemma lem4870588 {A : Type'} (_60261 : A -> Prop) : (@IN (A -> Prop) _60261) = (@IN (A -> Prop) _60261).
Proof. exact (eq_refl (@IN (A -> Prop) _60261)). Qed.
Lemma lem4870589 {A : Type'} (_60261 : A -> Prop) (u' : type686 A) (u : type686 A) : (term272 A _60261 u u') = (term308 A _60261 u' u).
Proof. exact (MK_COMB (@lem4870588 A _60261) (@lem4870587 A u' u)). Qed.
Lemma lem4870590 {A : Type'} (P : type686 A) (_60261 : A -> Prop) (u' : type686 A) (u : type686 A) (q' : Prop) : term309 A P _60261 u' u q'.
Proof. exact (@lem4870543 A u u' P _60261 (term308 A _60261 u' u) q'). Qed.
Lemma lem4870591 {A : Type'} (P : type686 A) (_60261 : A -> Prop) (u' : type686 A) (u : type686 A) (q' : Prop) : term310 A P _60261 u' u q'.
Proof. exact (@lem4870590 A P _60261 u' u q' (@lem4870589 A _60261 u' u)). Qed.
Lemma lem4870595 {A : Type'} (P : type686 A) (_60261 : A -> Prop) : (@UNION_OF A (@ARBITRARY A) P _60261) = (@UNION_OF A (@ARBITRARY A) P _60261).
Proof. exact (eq_refl (@UNION_OF A (@ARBITRARY A) P _60261)). Qed.
Lemma lem4870596 {A : Type'} (u' : type686 A) (u : type686 A) (P : type686 A) (_60261 : A -> Prop) : term311 A u' u P _60261.
Proof. exact (fun h0 : term308 A _60261 u' u => @lem4870595 A P _60261). Qed.
Lemma lem4870597 {A : Type'} (u' : type686 A) (u : type686 A) (P : type686 A) (_60261 : A -> Prop) : term312 A u' u P _60261.
Proof. exact (@lem4870591 A P _60261 u' u (@UNION_OF A (@ARBITRARY A) P _60261)). Qed.
Lemma lem4870598 {A : Type'} (u' : type686 A) (u : type686 A) (P : type686 A) (_60261 : A -> Prop) : (term313 A u u' P _60261) = (term314 A u' u P _60261).
Proof. exact (@lem4870597 A u' u P _60261 (@lem4870596 A u' u P _60261)). Qed.
Lemma lem4870624 {A : Type'} (u' : type686 A) (u : type686 A) (P : type686 A) : (term315 A u u' P) = (term316 A u' u P).
Proof. exact (fun_ext (fun _60261 : A -> Prop => @lem4870598 A u' u P _60261)). Qed.
Lemma lem4870702 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4870703 {A : Type'} (u' : type686 A) (u : type686 A) (P : type686 A) : (term317 A u u' P) = (term318 A u' u P).
Proof. exact (MK_COMB (@lem4870702 A) (@lem4870624 A u' u P)). Qed.
Lemma lem4870705 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term262 _87967 _87968 f s P) = (term263 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem4870376 _87967 _87968 s P f) (@lem4870375 _87967 _87968 P f s)). Qed.
Lemma lem4870706 {A : Type'} (s : type686 A) (P : type686 A) (f : type672 A) : (term319 A f s P) = (term320 A s P f).
Proof. exact (@lem4870705 (A -> Prop) (A -> Prop) s P f). Qed.
Lemma lem4870707 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) : (term321 A u' u P) = (term322 A u P u').
Proof. exact (@lem4870706 A u (term323 A P) (term304 A u')). Qed.
Lemma lem4870708 {A : Type'} (P : type686 A) (s : A -> Prop) : (term324 A P s) = (@UNION_OF A (@ARBITRARY A) P s).
Proof. exact (eq_refl (term324 A P s)). Qed.
Lemma lem4870709 {A : Type'} (s : A -> Prop) (u' : type686 A) (u : type686 A) : (term325 A s u' u) = (term325 A s u' u).
Proof. exact (eq_refl (term325 A s u' u)). Qed.
Lemma lem4870710 {A : Type'} (u' : type686 A) (u : type686 A) (P : type686 A) (s : A -> Prop) : (term326 A u' u P s) = (term314 A u' u P s).
Proof. exact (MK_COMB (@lem4870709 A s u' u) (@lem4870708 A P s)). Qed.
Lemma lem4870711 {A : Type'} (u' : type686 A) (u : type686 A) (P : type686 A) : (term327 A u' u P) = (term316 A u' u P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4870710 A u' u P s)). Qed.
Lemma lem4870712 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4870713 {A : Type'} (u' : type686 A) (u : type686 A) (P : type686 A) : (term321 A u' u P) = (term318 A u' u P).
Proof. exact (MK_COMB (@lem4870712 A) (@lem4870711 A u' u P)). Qed.
Lemma lem4870714 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4870715 {A : Type'} (u' : type686 A) (u : type686 A) (P : type686 A) : (term328 A u' u P) = (term329 A u' u P).
Proof. exact (MK_COMB (@lem4870714) (@lem4870713 A u' u P)). Qed.
Lemma lem4870716 {A : Type'} (P : type686 A) (u' : type686 A) (x : A -> Prop) : (term330 A P u' x) = (term331 A P u' x).
Proof. exact (eq_refl (term330 A P u' x)). Qed.
Lemma lem4870717 {A : Type'} (x : A -> Prop) (u : type686 A) : (term332 A x u) = (term332 A x u).
Proof. exact (eq_refl (term332 A x u)). Qed.
Lemma lem4870718 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) (x : A -> Prop) : (term333 A u P u' x) = (term334 A u P u' x).
Proof. exact (MK_COMB (@lem4870717 A x u) (@lem4870716 A P u' x)). Qed.
Lemma lem4870719 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) : (term335 A u P u') = (term336 A u P u').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4870718 A u P u' x)). Qed.
Lemma lem4870720 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4870721 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) : (term322 A u P u') = (term337 A u P u').
Proof. exact (MK_COMB (@lem4870720 A) (@lem4870719 A u P u')). Qed.
Lemma lem4870722 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) : ((term321 A u' u P) = (term322 A u P u')) = ((term318 A u' u P) = (term337 A u P u')).
Proof. exact (MK_COMB (@lem4870715 A u' u P) (@lem4870721 A u P u')). Qed.
Lemma lem4870723 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) : (term318 A u' u P) = (term337 A u P u').
Proof. exact (EQ_MP (@lem4870722 A u P u') (@lem4870707 A u P u')). Qed.
Lemma lem4870731 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term268 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4870732 (p : Prop) (q : Prop) (p' : Prop) : term269 p q p'.
Proof. exact (fun q' : Prop => @lem4870731 p q p' q'). Qed.
Lemma lem4870733 (p : Prop) (q : Prop) : term270 p q.
Proof. exact (fun p' : Prop => @lem4870732 p q p'). Qed.
Lemma lem4870734 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) (x : A -> Prop) : term338 A u P u' x.
Proof. exact (@lem4870733 (@IN (A -> Prop) x u) (term331 A P u' x)). Qed.
Lemma lem4870735 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) (x : A -> Prop) (p' : Prop) : term339 A u P u' x p'.
Proof. exact (@lem4870734 A u P u' x p'). Qed.
Lemma lem4870736 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) (x : A -> Prop) (p' : Prop) : (term339 A u P u' x p') = (term340 A u P u' x p').
Proof. exact (eq_refl (term339 A u P u' x p')). Qed.
Lemma lem4870737 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) (x : A -> Prop) (p' : Prop) : term340 A u P u' x p'.
Proof. exact (EQ_MP (@lem4870736 A u P u' x p') (@lem4870735 A u P u' x p')). Qed.
Lemma lem4870738 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) (x : A -> Prop) (p' : Prop) (q' : Prop) : term341 A u P u' x p' q'.
Proof. exact (@lem4870737 A u P u' x p' q'). Qed.
Lemma lem4870739 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) (x : A -> Prop) (p' : Prop) (q' : Prop) : (term341 A u P u' x p' q') = (term342 A u P u' x p' q').
Proof. exact (eq_refl (term341 A u P u' x p' q')). Qed.
Lemma lem4870740 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) (x : A -> Prop) (p' : Prop) (q' : Prop) : term342 A u P u' x p' q'.
Proof. exact (EQ_MP (@lem4870739 A u P u' x p' q') (@lem4870738 A u P u' x p' q')). Qed.
Lemma lem4870741 {A : Type'} (x : A -> Prop) (u : type686 A) : (@IN (A -> Prop) x u) = (@IN (A -> Prop) x u).
Proof. exact (eq_refl (@IN (A -> Prop) x u)). Qed.
Lemma lem4870742 {A : Type'} (P : type686 A) (u' : type686 A) (x : A -> Prop) (u : type686 A) (q' : Prop) : term343 A P u' x u q'.
Proof. exact (@lem4870740 A u P u' x (@IN (A -> Prop) x u) q'). Qed.
Lemma lem4870743 {A : Type'} (P : type686 A) (u' : type686 A) (x : A -> Prop) (u : type686 A) (q' : Prop) : term344 A P u' x u q'.
Proof. exact (@lem4870742 A P u' x u q' (@lem4870741 A x u)). Qed.
Lemma lem4870748 {A B : Type'} (f : A -> B) (y : A) : (term207 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4870749 {A : Type'} (f : type672 A) (y : A -> Prop) : (term345 A f y) = (f y).
Proof. exact (@lem4870748 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem4870750 {A : Type'} (u' : type686 A) (x : A -> Prop) : (term346 A u' x) = (term347 A u' x).
Proof. exact (@lem4870749 A (term304 A u') x). Qed.
Lemma lem4870751 {A : Type'} (x : A -> Prop) (u' : type686 A) : (term347 A u' x) = (term303 A x u').
Proof. exact (eq_refl (term347 A u' x)). Qed.
Lemma lem4870752 {A : Type'} (u' : type686 A) : (term348 A u') = (term304 A u').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4870751 A x u')). Qed.
Lemma lem4870753 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4870754 {A : Type'} (u' : type686 A) (x : A -> Prop) : (term346 A u' x) = (term347 A u' x).
Proof. exact (MK_COMB (@lem4870752 A u') (@lem4870753 A x)). Qed.
Lemma lem4870755 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4870756 {A : Type'} (u' : type686 A) (x : A -> Prop) : (term349 A u' x) = (term350 A u' x).
Proof. exact (MK_COMB (@lem4870755 A) (@lem4870754 A u' x)). Qed.
Lemma lem4870757 {A : Type'} (x : A -> Prop) (u' : type686 A) : (term347 A u' x) = (term303 A x u').
Proof. exact (eq_refl (term347 A u' x)). Qed.
Lemma lem4870758 {A : Type'} (x : A -> Prop) (u' : type686 A) : ((term346 A u' x) = (term347 A u' x)) = ((term347 A u' x) = (term303 A x u')).
Proof. exact (MK_COMB (@lem4870756 A u' x) (@lem4870757 A x u')). Qed.
Lemma lem4870759 {A : Type'} (x : A -> Prop) (u' : type686 A) : (term347 A u' x) = (term303 A x u').
Proof. exact (EQ_MP (@lem4870758 A x u') (@lem4870750 A u' x)). Qed.
Lemma lem4870760 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (@UNION_OF A (@ARBITRARY A) P).
Proof. exact (eq_refl (@UNION_OF A (@ARBITRARY A) P)). Qed.
Lemma lem4870761 {A : Type'} (P : type686 A) (x : A -> Prop) (u' : type686 A) : (term331 A P u' x) = (term351 A P x u').
Proof. exact (MK_COMB (@lem4870760 A P) (@lem4870759 A x u')). Qed.
Lemma lem4870762 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (u' : type686 A) : term352 A u P x u'.
Proof. exact (fun h0 : @IN (A -> Prop) x u => @lem4870761 A P x u'). Qed.
Lemma lem4870763 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (u' : type686 A) : term353 A u P x u'.
Proof. exact (@lem4870743 A P u' x u (term351 A P x u')). Qed.
Lemma lem4870764 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (u' : type686 A) : (term334 A u P u' x) = (term354 A u P x u').
Proof. exact (@lem4870763 A u P x u' (@lem4870762 A u P x u')). Qed.
Lemma lem4870788 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) : (term336 A u P u') = (term355 A u P u').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4870764 A u P x u')). Qed.
Lemma lem4870812 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4870813 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) : (term337 A u P u') = (term356 A u P u').
Proof. exact (MK_COMB (@lem4870812 A) (@lem4870788 A u P u')). Qed.
Lemma lem4870841 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) : (term318 A u' u P) = (term356 A u P u').
Proof. exact (TRANS (@lem4870723 A u P u') (@lem4870813 A u P u')). Qed.
Lemma lem4870842 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) : (term317 A u u' P) = (term356 A u P u').
Proof. exact (TRANS (@lem4870703 A u' u P) (@lem4870841 A u P u')). Qed.
Lemma lem4870843 {A : Type'} (u : type686 A) (u' : type686 A) (P : type686 A) : (term356 A u P u') = (term317 A u u' P).
Proof. exact (SYM (@lem4870842 A u P u')). Qed.
Lemma lem4870844 {A : Type'} (x : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) x u) : @IN (A -> Prop) x u.
Proof. exact (h1). Qed.
Lemma lem4870846 {A : Type'} (P : type686 A) (u : type686 A) : term4 A P u.
Proof. exact (EQ_MP (@lem4869098 A P u) (@lem4869097 A P u)). Qed.
Lemma lem4870847 {A : Type'} (P : type686 A) (u : type686 A) : term4 A P u.
Proof. exact (@lem4870846 A P u). Qed.
Lemma lem4870848 {A : Type'} (P : type686 A) (x : A -> Prop) (u' : type686 A) : term357 A P x u'.
Proof. exact (@lem4870847 A P (term289 A x u')). Qed.
Lemma lem4870849 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term259 _87967 _87968 P f.
Proof. exact (@lem3386920 _87967 _87968 P f). Qed.
Lemma lem4870850 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term259 _87967 _87968 P f) = (term260 _87967 _87968 P f).
Proof. exact (eq_refl (term259 _87967 _87968 P f)). Qed.
Lemma lem4870851 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term260 _87967 _87968 P f.
Proof. exact (EQ_MP (@lem4870850 _87967 _87968 P f) (@lem4870849 _87967 _87968 P f)). Qed.
Lemma lem4870852 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (s : _87968 -> Prop) : term261 _87967 _87968 P f s.
Proof. exact (@lem4870851 _87967 _87968 P f s). Qed.
Lemma lem4870853 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term261 _87967 _87968 P f s) = ((term262 _87967 _87968 f s P) = (term263 _87967 _87968 s P f)).
Proof. exact (eq_refl (term261 _87967 _87968 P f s)). Qed.
Lemma lem4870864 {A : Type'} (s : A -> Prop) (P : type686 A) (h1 : term45 A P) : term78 A P s.
Proof. exact (@lem4870137 A P h1 s). Qed.
Lemma lem4870865 {A : Type'} (P : type686 A) (s : A -> Prop) : (term78 A P s) = (term43 A P s).
Proof. exact (eq_refl (term78 A P s)). Qed.
Lemma lem4870866 {A : Type'} (s : A -> Prop) (P : type686 A) (h1 : term45 A P) : term43 A P s.
Proof. exact (EQ_MP (@lem4870865 A P s) (@lem4870864 A s P h1)). Qed.
Lemma lem4870867 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (h1 : term45 A P) : term71 A P s t.
Proof. exact (@lem4870866 A s P h1 t). Qed.
Lemma lem4870868 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term71 A P s t) = (term41 A P s t).
Proof. exact (eq_refl (term71 A P s t)). Qed.
Lemma lem4870869 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (h1 : term45 A P) : term41 A P s t.
Proof. exact (EQ_MP (@lem4870868 A P s t) (@lem4870867 A s t P h1)). Qed.
Lemma lem4870870 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) (h1 : term66 A s P t) : term66 A s P t.
Proof. exact (h1). Qed.
Lemma lem4870871 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) (h1 : term45 A P) (h2 : term66 A s P t) : term54 A P s t.
Proof. exact (@lem4870869 A s t P h1 (@lem4870870 A s P t h2)). Qed.
Lemma lem4870872 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term54 A P s t) = ((term54 A P s t) = True).
Proof. exact (@lem7 (term54 A P s t)). Qed.
Lemma lem4870873 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) (h1 : term45 A P) (h2 : term66 A s P t) : (term54 A P s t) = True.
Proof. exact (EQ_MP (@lem4870872 A P s t) (@lem4870871 A s P t h1 h2)). Qed.
Lemma lem4870881 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term229 A u P) : term358 A u P c.
Proof. exact (@lem4870284 A u P h1 c). Qed.
Lemma lem4870882 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term358 A u P c) = (term359 A u P c).
Proof. exact (eq_refl (term358 A u P c)). Qed.
Lemma lem4870883 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term229 A u P) : term359 A u P c.
Proof. exact (EQ_MP (@lem4870882 A u P c) (@lem4870881 A c u P h1)). Qed.
Lemma lem4870884 {A : Type'} (c : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) c u) : @IN (A -> Prop) c u.
Proof. exact (h1). Qed.
Lemma lem4870885 {A : Type'} (P : type686 A) (c : A -> Prop) (u : type686 A) (h1 : term229 A u P) (h2 : @IN (A -> Prop) c u) : P c.
Proof. exact (@lem4870883 A c u P h1 (@lem4870884 A c u h2)). Qed.
Lemma lem4870886 {A : Type'} (P : type686 A) (c : A -> Prop) : (P c) = ((P c) = True).
Proof. exact (@lem7 (P c)). Qed.
Lemma lem4870887 {A : Type'} (P : type686 A) (c : A -> Prop) (u : type686 A) (h1 : term229 A u P) (h2 : @IN (A -> Prop) c u) : (P c) = True.
Proof. exact (EQ_MP (@lem4870886 A P c) (@lem4870885 A P c u h1 h2)). Qed.
Lemma lem4870895 {A : Type'} (c : A -> Prop) (u' : type686 A) (P : type686 A) (h1 : term229 A u' P) : term358 A u' P c.
Proof. exact (@lem4870289 A u' P h1 c). Qed.
Lemma lem4870896 {A : Type'} (u' : type686 A) (P : type686 A) (c : A -> Prop) : (term358 A u' P c) = (term359 A u' P c).
Proof. exact (eq_refl (term358 A u' P c)). Qed.
Lemma lem4870897 {A : Type'} (c : A -> Prop) (u' : type686 A) (P : type686 A) (h1 : term229 A u' P) : term359 A u' P c.
Proof. exact (EQ_MP (@lem4870896 A u' P c) (@lem4870895 A c u' P h1)). Qed.
Lemma lem4870898 {A : Type'} (c : A -> Prop) (u' : type686 A) (h1 : @IN (A -> Prop) c u') : @IN (A -> Prop) c u'.
Proof. exact (h1). Qed.
Lemma lem4870899 {A : Type'} (P : type686 A) (c : A -> Prop) (u' : type686 A) (h1 : term229 A u' P) (h2 : @IN (A -> Prop) c u') : P c.
Proof. exact (@lem4870897 A c u' P h1 (@lem4870898 A c u' h2)). Qed.
Lemma lem4870900 {A : Type'} (P : type686 A) (c : A -> Prop) : (P c) = ((P c) = True).
Proof. exact (@lem7 (P c)). Qed.
Lemma lem4870901 {A : Type'} (P : type686 A) (c : A -> Prop) (u' : type686 A) (h1 : term229 A u' P) (h2 : @IN (A -> Prop) c u') : (P c) = True.
Proof. exact (EQ_MP (@lem4870900 A P c) (@lem4870899 A P c u' h1 h2)). Qed.
Lemma lem4870907 {A : Type'} (x : A -> Prop) (u : type686 A) : (@IN (A -> Prop) x u) = ((@IN (A -> Prop) x u) = True).
Proof. exact (@lem7 (@IN (A -> Prop) x u)). Qed.
Lemma lem4870910 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term262 _87967 _87968 f s P) = (term263 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem4870853 _87967 _87968 s P f) (@lem4870852 _87967 _87968 P f s)). Qed.
Lemma lem4870911 {A : Type'} (s : type686 A) (P : type686 A) (f : type672 A) : (term319 A f s P) = (term320 A s P f).
Proof. exact (@lem4870910 (A -> Prop) (A -> Prop) s P f). Qed.
Lemma lem4870912 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) : (term360 A x u' P) = (term361 A u' P x).
Proof. exact (@lem4870911 A u' (term323 A P) (term290 A x)). Qed.
Lemma lem4870913 {A : Type'} (P : type686 A) (s : A -> Prop) : (term324 A P s) = (@UNION_OF A (@ARBITRARY A) P s).
Proof. exact (eq_refl (term324 A P s)). Qed.
Lemma lem4870914 {A : Type'} (s : A -> Prop) (x : A -> Prop) (u' : type686 A) : (term362 A s x u') = (term362 A s x u').
Proof. exact (eq_refl (term362 A s x u')). Qed.
Lemma lem4870915 {A : Type'} (x : A -> Prop) (u' : type686 A) (P : type686 A) (s : A -> Prop) : (term363 A x u' P s) = (term364 A x u' P s).
Proof. exact (MK_COMB (@lem4870914 A s x u') (@lem4870913 A P s)). Qed.
Lemma lem4870916 {A : Type'} (x : A -> Prop) (u' : type686 A) (P : type686 A) : (term365 A x u' P) = (term366 A x u' P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4870915 A x u' P s)). Qed.
Lemma lem4870917 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4870918 {A : Type'} (x : A -> Prop) (u' : type686 A) (P : type686 A) : (term360 A x u' P) = (term367 A x u' P).
Proof. exact (MK_COMB (@lem4870917 A) (@lem4870916 A x u' P)). Qed.
Lemma lem4870919 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4870920 {A : Type'} (x : A -> Prop) (u' : type686 A) (P : type686 A) : (term368 A x u' P) = (term369 A x u' P).
Proof. exact (MK_COMB (@lem4870919) (@lem4870918 A x u' P)). Qed.
Lemma lem4870921 {A : Type'} (P : type686 A) (x : A -> Prop) (x' : A -> Prop) : (term370 A P x x') = (term371 A P x x').
Proof. exact (eq_refl (term370 A P x x')). Qed.
Lemma lem4870922 {A : Type'} (x' : A -> Prop) (u' : type686 A) : (term332 A x' u') = (term332 A x' u').
Proof. exact (eq_refl (term332 A x' u')). Qed.
Lemma lem4870923 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (x' : A -> Prop) : (term372 A u' P x x') = (term373 A u' P x x').
Proof. exact (MK_COMB (@lem4870922 A x' u') (@lem4870921 A P x x')). Qed.
Lemma lem4870924 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) : (term374 A u' P x) = (term375 A u' P x).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4870923 A u' P x x')). Qed.
Lemma lem4870925 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4870926 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) : (term361 A u' P x) = (term376 A u' P x).
Proof. exact (MK_COMB (@lem4870925 A) (@lem4870924 A u' P x)). Qed.
Lemma lem4870927 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) : ((term360 A x u' P) = (term361 A u' P x)) = ((term367 A x u' P) = (term376 A u' P x)).
Proof. exact (MK_COMB (@lem4870920 A x u' P) (@lem4870926 A u' P x)). Qed.
Lemma lem4870928 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) : (term367 A x u' P) = (term376 A u' P x).
Proof. exact (EQ_MP (@lem4870927 A u' P x) (@lem4870912 A u' P x)). Qed.
Lemma lem4870936 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term268 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4870937 (p : Prop) (q : Prop) (p' : Prop) : term269 p q p'.
Proof. exact (fun q' : Prop => @lem4870936 p q p' q'). Qed.
Lemma lem4870938 (p : Prop) (q : Prop) : term270 p q.
Proof. exact (fun p' : Prop => @lem4870937 p q p'). Qed.
Lemma lem4870939 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (x' : A -> Prop) : term377 A u' P x x'.
Proof. exact (@lem4870938 (@IN (A -> Prop) x' u') (term371 A P x x')). Qed.
Lemma lem4870940 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (x' : A -> Prop) (p' : Prop) : term378 A u' P x x' p'.
Proof. exact (@lem4870939 A u' P x x' p'). Qed.
Lemma lem4870941 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (x' : A -> Prop) (p' : Prop) : (term378 A u' P x x' p') = (term379 A u' P x x' p').
Proof. exact (eq_refl (term378 A u' P x x' p')). Qed.
Lemma lem4870942 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (x' : A -> Prop) (p' : Prop) : term379 A u' P x x' p'.
Proof. exact (EQ_MP (@lem4870941 A u' P x x' p') (@lem4870940 A u' P x x' p')). Qed.
Lemma lem4870943 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (x' : A -> Prop) (p' : Prop) (q' : Prop) : term380 A u' P x x' p' q'.
Proof. exact (@lem4870942 A u' P x x' p' q'). Qed.
Lemma lem4870944 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (x' : A -> Prop) (p' : Prop) (q' : Prop) : (term380 A u' P x x' p' q') = (term381 A u' P x x' p' q').
Proof. exact (eq_refl (term380 A u' P x x' p' q')). Qed.
Lemma lem4870945 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (x' : A -> Prop) (p' : Prop) (q' : Prop) : term381 A u' P x x' p' q'.
Proof. exact (EQ_MP (@lem4870944 A u' P x x' p' q') (@lem4870943 A u' P x x' p' q')). Qed.
Lemma lem4870946 {A : Type'} (x' : A -> Prop) (u' : type686 A) : (@IN (A -> Prop) x' u') = (@IN (A -> Prop) x' u').
Proof. exact (eq_refl (@IN (A -> Prop) x' u')). Qed.
Lemma lem4870947 {A : Type'} (P : type686 A) (x : A -> Prop) (x' : A -> Prop) (u' : type686 A) (q' : Prop) : term382 A P x x' u' q'.
Proof. exact (@lem4870945 A u' P x x' (@IN (A -> Prop) x' u') q'). Qed.
Lemma lem4870948 {A : Type'} (P : type686 A) (x : A -> Prop) (x' : A -> Prop) (u' : type686 A) (q' : Prop) : term383 A P x x' u' q'.
Proof. exact (@lem4870947 A P x x' u' q' (@lem4870946 A x' u')). Qed.
Lemma lem4870949 {A : Type'} (x' : A -> Prop) (u' : type686 A) (h1 : @IN (A -> Prop) x' u') : @IN (A -> Prop) x' u'.
Proof. exact (h1). Qed.
Lemma lem4870950 {A : Type'} (x' : A -> Prop) (u' : type686 A) : (@IN (A -> Prop) x' u') = ((@IN (A -> Prop) x' u') = True).
Proof. exact (@lem7 (@IN (A -> Prop) x' u')). Qed.
Lemma lem4870953 {A B : Type'} (f : A -> B) (y : A) : (term207 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4870954 {A : Type'} (f : type672 A) (y : A -> Prop) : (term345 A f y) = (f y).
Proof. exact (@lem4870953 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem4870955 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term384 A x x') = (term291 A x x').
Proof. exact (@lem4870954 A (term290 A x) x'). Qed.
Lemma lem4870956 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term291 A x x') = (@INTER A x x').
Proof. exact (eq_refl (term291 A x x')). Qed.
Lemma lem4870957 {A : Type'} (x : A -> Prop) : (term385 A x) = (term290 A x).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4870956 A x x')). Qed.
Lemma lem4870958 {A : Type'} (x' : A -> Prop) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem4870959 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term384 A x x') = (term291 A x x').
Proof. exact (MK_COMB (@lem4870957 A x) (@lem4870958 A x')). Qed.
Lemma lem4870960 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4870961 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term386 A x x') = (term387 A x x').
Proof. exact (MK_COMB (@lem4870960 A) (@lem4870959 A x x')). Qed.
Lemma lem4870962 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term291 A x x') = (@INTER A x x').
Proof. exact (eq_refl (term291 A x x')). Qed.
Lemma lem4870963 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : ((term384 A x x') = (term291 A x x')) = ((term291 A x x') = (@INTER A x x')).
Proof. exact (MK_COMB (@lem4870961 A x x') (@lem4870962 A x x')). Qed.
Lemma lem4870964 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term291 A x x') = (@INTER A x x').
Proof. exact (EQ_MP (@lem4870963 A x x') (@lem4870955 A x x')). Qed.
Lemma lem4870965 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (@UNION_OF A (@ARBITRARY A) P).
Proof. exact (eq_refl (@UNION_OF A (@ARBITRARY A) P)). Qed.
Lemma lem4870966 {A : Type'} (P : type686 A) (x : A -> Prop) (x' : A -> Prop) : (term371 A P x x') = (term54 A P x x').
Proof. exact (MK_COMB (@lem4870965 A P) (@lem4870964 A x x')). Qed.
Lemma lem4870968 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (h1 : term45 A P) : term388 A P s t.
Proof. exact (fun h0 : term66 A s P t => @lem4870873 A s P t h1 h0). Qed.
Lemma lem4870969 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (h1 : term45 A P) : term388 A P s t.
Proof. exact (@lem4870968 A s t P h1). Qed.
Lemma lem4870970 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (P : type686 A) (h1 : term45 A P) : term388 A P x x'.
Proof. exact (@lem4870969 A x x' P h1). Qed.
Lemma lem4870974 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term229 A u P) : term389 A u P c.
Proof. exact (fun h0 : @IN (A -> Prop) c u => @lem4870887 A P c u h1 h0). Qed.
Lemma lem4870975 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term229 A u P) : term389 A u P c.
Proof. exact (@lem4870974 A c u P h1). Qed.
Lemma lem4870976 {A : Type'} (x : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term229 A u P) : term389 A u P x.
Proof. exact (@lem4870975 A x u P h1). Qed.
Lemma lem4870978 {A : Type'} (x : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) x u) : (@IN (A -> Prop) x u) = True.
Proof. exact (EQ_MP (@lem4870907 A x u) (@lem4870844 A x u h1)). Qed.
Lemma lem4870979 {A : Type'} (x : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) x u) : True = (@IN (A -> Prop) x u).
Proof. exact (SYM (@lem4870978 A x u h1)). Qed.
Lemma lem4870980 {A : Type'} (x : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) x u) : @IN (A -> Prop) x u.
Proof. exact (EQ_MP (@lem4870979 A x u h1) (@lem0)). Qed.
Lemma lem4870981 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term229 A u P) (h2 : @IN (A -> Prop) x u) : (P x) = True.
Proof. exact (@lem4870976 A x u P h1 (@lem4870980 A x u h2)). Qed.
Lemma lem4870982 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4870983 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term229 A u P) (h2 : @IN (A -> Prop) x u) : (term140 A P x) = (and True).
Proof. exact (MK_COMB (@lem4870982) (@lem4870981 A P x u h1 h2)). Qed.
Lemma lem4870991 {A : Type'} (c : A -> Prop) (u' : type686 A) (P : type686 A) (h1 : term229 A u' P) : term389 A u' P c.
Proof. exact (fun h0 : @IN (A -> Prop) c u' => @lem4870901 A P c u' h1 h0). Qed.
Lemma lem4870992 {A : Type'} (c : A -> Prop) (u' : type686 A) (P : type686 A) (h1 : term229 A u' P) : term389 A u' P c.
Proof. exact (@lem4870991 A c u' P h1). Qed.
Lemma lem4870993 {A : Type'} (x' : A -> Prop) (u' : type686 A) (P : type686 A) (h1 : term229 A u' P) : term389 A u' P x'.
Proof. exact (@lem4870992 A x' u' P h1). Qed.
Lemma lem4870995 {A : Type'} (x' : A -> Prop) (u' : type686 A) (h1 : @IN (A -> Prop) x' u') : (@IN (A -> Prop) x' u') = True.
Proof. exact (EQ_MP (@lem4870950 A x' u') (@lem4870949 A x' u' h1)). Qed.
Lemma lem4870996 {A : Type'} (x' : A -> Prop) (u' : type686 A) (h1 : @IN (A -> Prop) x' u') : True = (@IN (A -> Prop) x' u').
Proof. exact (SYM (@lem4870995 A x' u' h1)). Qed.
Lemma lem4870997 {A : Type'} (x' : A -> Prop) (u' : type686 A) (h1 : @IN (A -> Prop) x' u') : @IN (A -> Prop) x' u'.
Proof. exact (EQ_MP (@lem4870996 A x' u' h1) (@lem0)). Qed.
Lemma lem4870998 {A : Type'} (P : type686 A) (x' : A -> Prop) (u' : type686 A) (h1 : term229 A u' P) (h2 : @IN (A -> Prop) x' u') : (P x') = True.
Proof. exact (@lem4870993 A x' u' P h1 (@lem4870997 A x' u' h2)). Qed.
Lemma lem4870999 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (u' : type686 A) (h1 : term229 A u P) (h2 : term229 A u' P) (h3 : @IN (A -> Prop) x u) (h4 : @IN (A -> Prop) x' u') : (term66 A x P x') = (True /\ True).
Proof. exact (MK_COMB (@lem4870983 A P x u h1 h3) (@lem4870998 A P x' u' h2 h4)). Qed.
Lemma lem4871001 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4871002 : (True /\ True) = True.
Proof. exact (@lem4871001 True). Qed.
Lemma lem4871003 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (u' : type686 A) (h1 : term229 A u P) (h2 : term229 A u' P) (h3 : @IN (A -> Prop) x u) (h4 : @IN (A -> Prop) x' u') : (term66 A x P x') = True.
Proof. exact (TRANS (@lem4870999 A P x u x' u' h1 h2 h3 h4) (@lem4871002)). Qed.
Lemma lem4871004 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (u' : type686 A) (h1 : term229 A u P) (h2 : term229 A u' P) (h3 : @IN (A -> Prop) x u) (h4 : @IN (A -> Prop) x' u') : True = (term66 A x P x').
Proof. exact (SYM (@lem4871003 A P x u x' u' h1 h2 h3 h4)). Qed.
Lemma lem4871005 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (u' : type686 A) (h1 : term229 A u P) (h2 : term229 A u' P) (h3 : @IN (A -> Prop) x u) (h4 : @IN (A -> Prop) x' u') : term66 A x P x'.
Proof. exact (EQ_MP (@lem4871004 A P x u x' u' h1 h2 h3 h4) (@lem0)). Qed.
Lemma lem4871006 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (u' : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @IN (A -> Prop) x u) (h5 : @IN (A -> Prop) x' u') : (term54 A P x x') = True.
Proof. exact (@lem4870970 A x x' P h1 (@lem4871005 A P x u x' u' h2 h3 h4 h5)). Qed.
Lemma lem4871007 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (u' : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @IN (A -> Prop) x u) (h5 : @IN (A -> Prop) x' u') : (term371 A P x x') = True.
Proof. exact (TRANS (@lem4870966 A P x x') (@lem4871006 A P x u x' u' h1 h2 h3 h4 h5)). Qed.
Lemma lem4871008 {A : Type'} (x' : A -> Prop) (u' : type686 A) (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @IN (A -> Prop) x u) : term390 A u' P x x'.
Proof. exact (fun h0 : @IN (A -> Prop) x' u' => @lem4871007 A P x u x' u' h1 h2 h3 h4 h0). Qed.
Lemma lem4871009 {A : Type'} (P : type686 A) (x : A -> Prop) (x' : A -> Prop) (u' : type686 A) : term391 A P x x' u'.
Proof. exact (@lem4870948 A P x x' u' True). Qed.
Lemma lem4871010 {A : Type'} (x' : A -> Prop) (u' : type686 A) (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @IN (A -> Prop) x u) : (term373 A u' P x x') = (term392 A x' u').
Proof. exact (@lem4871009 A P x x' u' (@lem4871008 A x' u' P x u h1 h2 h3 h4)). Qed.
Lemma lem4871012 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4871013 {A : Type'} (x' : A -> Prop) (u' : type686 A) : (term392 A x' u') = True.
Proof. exact (@lem4871012 (@IN (A -> Prop) x' u')). Qed.
Lemma lem4871014 {A : Type'} (x' : A -> Prop) (u' : type686 A) (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @IN (A -> Prop) x u) : (term373 A u' P x x') = True.
Proof. exact (TRANS (@lem4871010 A x' u' P x u h1 h2 h3 h4) (@lem4871013 A x' u')). Qed.
Lemma lem4871015 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @IN (A -> Prop) x u) : (term375 A u' P x) = (term393 A).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4871014 A x' u' P x u h1 h2 h3 h4)). Qed.
Lemma lem4871016 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4871017 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @IN (A -> Prop) x u) : (term376 A u' P x) = (term394 A).
Proof. exact (MK_COMB (@lem4871016 A) (@lem4871015 A u' P x u h1 h2 h3 h4)). Qed.
Lemma lem4871019 {A : Type'} (t : Prop) : (term395 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4871020 {A : Type'} (t : Prop) : (term396 A t) = t.
Proof. exact (@lem4871019 (A -> Prop) t). Qed.
Lemma lem4871021 {A : Type'} : (term394 A) = True.
Proof. exact (@lem4871020 A True). Qed.
Lemma lem4871022 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @IN (A -> Prop) x u) : (term376 A u' P x) = True.
Proof. exact (TRANS (@lem4871017 A u' P x u h1 h2 h3 h4) (@lem4871021 A)). Qed.
Lemma lem4871023 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @IN (A -> Prop) x u) : (term367 A x u' P) = True.
Proof. exact (TRANS (@lem4870928 A u' P x) (@lem4871022 A u' P x u h1 h2 h3 h4)). Qed.
Lemma lem4871024 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @IN (A -> Prop) x u) : True = (term367 A x u' P).
Proof. exact (SYM (@lem4871023 A u' P x u h1 h2 h3 h4)). Qed.
Lemma lem4871025 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @IN (A -> Prop) x u) : term367 A x u' P.
Proof. exact (EQ_MP (@lem4871024 A u' P x u h1 h2 h3 h4) (@lem0)). Qed.
Lemma lem4871026 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @IN (A -> Prop) x u) : term351 A P x u'.
Proof. exact (@lem4870848 A P x u' (@lem4871025 A u' P x u h1 h2 h3 h4)). Qed.
Lemma lem4871027 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @IN (A -> Prop) x u) : (@IN (A -> Prop) x u) = (term351 A P x u').
Proof. exact (prop_ext (fun h5 : @IN (A -> Prop) x u => @lem4871026 A u' P x u h1 h2 h3 h4) (fun h5 : term351 A P x u' => @lem4870844 A x u h4)). Qed.
Lemma lem4871028 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @IN (A -> Prop) x u) : term351 A P x u'.
Proof. exact (EQ_MP (@lem4871027 A u' P x u h1 h2 h3 h4) (@lem4870844 A x u h4)). Qed.
Lemma lem4871029 {A : Type'} (x : A -> Prop) (u : type686 A) (u' : type686 A) (P : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) : term354 A u P x u'.
Proof. exact (fun h0 : @IN (A -> Prop) x u => @lem4871028 A u' P x u h1 h2 h3 h0). Qed.
Lemma lem4871034 {A : Type'} (u : type686 A) (u' : type686 A) (P : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) : term356 A u P u'.
Proof. exact (fun x : A -> Prop => @lem4871029 A x u u' P h1 h2 h3). Qed.
Lemma lem4871035 {A : Type'} (u : type686 A) (u' : type686 A) (P : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) : term317 A u u' P.
Proof. exact (EQ_MP (@lem4870843 A u u' P) (@lem4871034 A u u' P h1 h2 h3)). Qed.
Lemma lem4871036 {A : Type'} (u : type686 A) (u' : type686 A) (P : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) : term257 A P u u'.
Proof. exact (@lem4870371 A P u u' (@lem4871035 A u u' P h1 h2 h3)). Qed.
Lemma lem4871037 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : s = (@UNIONS A u)) (h5 : t = (@UNIONS A u')) : term54 A P s t.
Proof. exact (EQ_MP (@lem4870367 A P s u t u' h4 h5) (@lem4871036 A u u' P h1 h2 h3)). Qed.
Lemma lem4871038 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) (h1 : term215 A s P t) : term226 A P t.
Proof. exact (proj2 (@lem4870277 A s P t h1)). Qed.
Lemma lem4871039 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) (h1 : term215 A s P t) : term226 A P s.
Proof. exact (proj1 (@lem4870277 A s P t h1)). Qed.
Lemma lem4871040 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : term223 A P t u') : term220 A P t u'.
Proof. exact (proj2 (@lem4870285 A P t u' h1)). Qed.
Lemma lem4871042 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : term220 A P t u') : t = (@UNIONS A u').
Proof. exact (proj2 (@lem4870286 A P t u' h1)). Qed.
Lemma lem4871043 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : term220 A P t u') : term229 A u' P.
Proof. exact (proj1 (@lem4870286 A P t u' h1)). Qed.
Lemma lem4871044 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : s = (@UNIONS A u)) (h5 : t = (@UNIONS A u')) : (t = (@UNIONS A u')) = (term54 A P s t).
Proof. exact (prop_ext (fun h6 : t = (@UNIONS A u') => @lem4871037 A P s u t u' h1 h2 h3 h4 h5) (fun h6 : term54 A P s t => @lem4870288 A t u' h5)). Qed.
Lemma lem4871045 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : s = (@UNIONS A u)) (h5 : t = (@UNIONS A u')) : term54 A P s t.
Proof. exact (EQ_MP (@lem4871044 A P s u t u' h1 h2 h3 h4 h5) (@lem4870288 A t u' h5)). Qed.
Lemma lem4871046 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : s = (@UNIONS A u)) (h5 : t = (@UNIONS A u')) : (term229 A u' P) = (term54 A P s t).
Proof. exact (prop_ext (fun h6 : term229 A u' P => @lem4871045 A P s u t u' h1 h2 h3 h4 h5) (fun h6 : term54 A P s t => @lem4870289 A u' P h3)). Qed.
Lemma lem4871047 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : s = (@UNIONS A u)) (h5 : t = (@UNIONS A u')) : term54 A P s t.
Proof. exact (EQ_MP (@lem4871046 A P s u t u' h1 h2 h3 h4 h5) (@lem4870289 A u' P h3)). Qed.
Lemma lem4871048 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : term220 A P t u') (h5 : s = (@UNIONS A u)) : (t = (@UNIONS A u')) = (term54 A P s t).
Proof. exact (prop_ext (fun h6 : t = (@UNIONS A u') => @lem4871047 A P s u t u' h1 h2 h3 h5 h6) (fun h6 : term54 A P s t => @lem4871042 A P t u' h4)). Qed.
Lemma lem4871049 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : term220 A P t u') (h5 : s = (@UNIONS A u)) : term54 A P s t.
Proof. exact (EQ_MP (@lem4871048 A P t u' s u h1 h2 h3 h4 h5) (@lem4871042 A P t u' h4)). Qed.
Lemma lem4871050 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term220 A P t u') (h4 : s = (@UNIONS A u)) : (term229 A u' P) = (term54 A P s t).
Proof. exact (prop_ext (fun h5 : term229 A u' P => @lem4871049 A P t u' s u h1 h2 h5 h3 h4) (fun h5 : term54 A P s t => @lem4871043 A P t u' h3)). Qed.
Lemma lem4871051 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term220 A P t u') (h4 : s = (@UNIONS A u)) : term54 A P s t.
Proof. exact (EQ_MP (@lem4871050 A P t u' s u h1 h2 h3 h4) (@lem4871043 A P t u' h3)). Qed.
Lemma lem4871052 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term223 A P t u') (h4 : s = (@UNIONS A u)) : (term220 A P t u') = (term54 A P s t).
Proof. exact (prop_ext (fun h5 : term220 A P t u' => @lem4871051 A P t u' s u h1 h2 h5 h4) (fun h5 : term54 A P s t => @lem4871040 A P t u' h3)). Qed.
Lemma lem4871053 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term223 A P t u') (h4 : s = (@UNIONS A u)) : term54 A P s t.
Proof. exact (EQ_MP (@lem4871052 A P t u' s u h1 h2 h3 h4) (@lem4871040 A P t u' h3)). Qed.
Lemma lem4871054 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term226 A P t) (h4 : s = (@UNIONS A u)) : term54 A P s t.
Proof. exact (ex_elim (@lem4870278 A P t h3) (fun u' : type686 A => fun h0 : term225 A P t u' => @lem4871053 A P t u' s u h1 h2 h0 h4)). Qed.
Lemma lem4871055 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term223 A P s u) : term220 A P s u.
Proof. exact (proj2 (@lem4870280 A P s u h1)). Qed.
Lemma lem4871057 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term220 A P s u) : s = (@UNIONS A u).
Proof. exact (proj2 (@lem4870281 A P s u h1)). Qed.
Lemma lem4871058 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term220 A P s u) : term229 A u P.
Proof. exact (proj1 (@lem4870281 A P s u h1)). Qed.
Lemma lem4871059 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term226 A P t) (h4 : s = (@UNIONS A u)) : (s = (@UNIONS A u)) = (term54 A P s t).
Proof. exact (prop_ext (fun h5 : s = (@UNIONS A u) => @lem4871054 A P t s u h1 h2 h3 h4) (fun h5 : term54 A P s t => @lem4870283 A s u h4)). Qed.
Lemma lem4871060 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term226 A P t) (h4 : s = (@UNIONS A u)) : term54 A P s t.
Proof. exact (EQ_MP (@lem4871059 A P t s u h1 h2 h3 h4) (@lem4870283 A s u h4)). Qed.
Lemma lem4871061 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term226 A P t) (h4 : s = (@UNIONS A u)) : (term229 A u P) = (term54 A P s t).
Proof. exact (prop_ext (fun h5 : term229 A u P => @lem4871060 A P t s u h1 h2 h3 h4) (fun h5 : term54 A P s t => @lem4870284 A u P h2)). Qed.
Lemma lem4871062 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term226 A P t) (h4 : s = (@UNIONS A u)) : term54 A P s t.
Proof. exact (EQ_MP (@lem4871061 A P t s u h1 h2 h3 h4) (@lem4870284 A u P h2)). Qed.
Lemma lem4871063 {A : Type'} (t : A -> Prop) (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term226 A P t) (h4 : term220 A P s u) : (s = (@UNIONS A u)) = (term54 A P s t).
Proof. exact (prop_ext (fun h5 : s = (@UNIONS A u) => @lem4871062 A P t s u h1 h2 h3 h5) (fun h5 : term54 A P s t => @lem4871057 A P s u h4)). Qed.
Lemma lem4871064 {A : Type'} (t : A -> Prop) (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term226 A P t) (h4 : term220 A P s u) : term54 A P s t.
Proof. exact (EQ_MP (@lem4871063 A t P s u h1 h2 h3 h4) (@lem4871057 A P s u h4)). Qed.
Lemma lem4871065 {A : Type'} (t : A -> Prop) (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term226 A P t) (h3 : term220 A P s u) : (term229 A u P) = (term54 A P s t).
Proof. exact (prop_ext (fun h4 : term229 A u P => @lem4871064 A t P s u h1 h4 h2 h3) (fun h4 : term54 A P s t => @lem4871058 A P s u h3)). Qed.
Lemma lem4871066 {A : Type'} (t : A -> Prop) (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term226 A P t) (h3 : term220 A P s u) : term54 A P s t.
Proof. exact (EQ_MP (@lem4871065 A t P s u h1 h2 h3) (@lem4871058 A P s u h3)). Qed.
Lemma lem4871067 {A : Type'} (t : A -> Prop) (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term226 A P t) (h3 : term223 A P s u) : (term220 A P s u) = (term54 A P s t).
Proof. exact (prop_ext (fun h4 : term220 A P s u => @lem4871066 A t P s u h1 h2 h4) (fun h4 : term54 A P s t => @lem4871055 A P s u h3)). Qed.
Lemma lem4871068 {A : Type'} (t : A -> Prop) (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term226 A P t) (h3 : term223 A P s u) : term54 A P s t.
Proof. exact (EQ_MP (@lem4871067 A t P s u h1 h2 h3) (@lem4871055 A P s u h3)). Qed.
Lemma lem4871069 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) (h1 : term45 A P) (h2 : term226 A P s) (h3 : term226 A P t) : term54 A P s t.
Proof. exact (ex_elim (@lem4870279 A P s h2) (fun u : type686 A => fun h0 : term225 A P s u => @lem4871068 A t P s u h1 h3 h0)). Qed.
Lemma lem4871070 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) (h1 : term45 A P) (h2 : term226 A P s) (h3 : term215 A s P t) : (term226 A P t) = (term54 A P s t).
Proof. exact (prop_ext (fun h4 : term226 A P t => @lem4871069 A s P t h1 h2 h4) (fun h4 : term54 A P s t => @lem4871038 A s P t h3)). Qed.
Lemma lem4871071 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) (h1 : term45 A P) (h2 : term226 A P s) (h3 : term215 A s P t) : term54 A P s t.
Proof. exact (EQ_MP (@lem4871070 A s P t h1 h2 h3) (@lem4871038 A s P t h3)). Qed.
Lemma lem4871072 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) (h1 : term45 A P) (h2 : term215 A s P t) : (term226 A P s) = (term54 A P s t).
Proof. exact (prop_ext (fun h3 : term226 A P s => @lem4871071 A s P t h1 h3 h2) (fun h3 : term54 A P s t => @lem4871039 A s P t h2)). Qed.
Lemma lem4871073 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) (h1 : term45 A P) (h2 : term215 A s P t) : term54 A P s t.
Proof. exact (EQ_MP (@lem4871072 A s P t h1 h2) (@lem4871039 A s P t h2)). Qed.
Lemma lem4871074 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (h1 : term45 A P) : term217 A P s t.
Proof. exact (fun h0 : term215 A s P t => @lem4871073 A s P t h1 h0). Qed.
Lemma lem4871075 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (h1 : term45 A P) : term206 A P s t.
Proof. exact (EQ_MP (@lem4870231 A P s t) (@lem4871074 A s t P h1)). Qed.
Lemma lem4871076 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (h1 : term45 A P) : term46 A P s t.
Proof. exact (EQ_MP (@lem4870157 A P s t) (@lem4871075 A s t P h1)). Qed.
Lemma lem4871081 {A : Type'} (s : A -> Prop) (P : type686 A) (h1 : term45 A P) : term48 A P s.
Proof. exact (fun t : A -> Prop => @lem4871076 A s t P h1). Qed.
Lemma lem4871086 {A : Type'} (P : type686 A) (h1 : term45 A P) : term50 A P.
Proof. exact (fun s : A -> Prop => @lem4871081 A s P h1). Qed.
Lemma lem4871087 {A : Type'} (P : type686 A) : term397 A P.
Proof. exact (fun h0 : term45 A P => @lem4871086 A P h0). Qed.
Lemma lem4871088 {A : Type'} (P : type686 A) : term398 A P.
Proof. exact (conj (@lem4870136 A P) (@lem4871087 A P)). Qed.
Lemma lem4871089 {A : Type'} (P : type686 A) : (term398 A P) = ((term50 A P) = (term45 A P)).
Proof. exact (@lem32 (term50 A P) (term45 A P)). Qed.
Lemma lem4871090 {A : Type'} (P : type686 A) : (term50 A P) = (term45 A P).
Proof. exact (EQ_MP (@lem4871089 A P) (@lem4871088 A P)). Qed.
Lemma lem4871095 {A : Type'} : term399 A.
Proof. exact (fun P : type686 A => @lem4871090 A P). Qed.
