Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_UNION_EQ_term_abbrevs.
Require Import DISJOINT_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_SUBSET_spec.
Require Import NSUM_UNION_spec.
Require Import SUBSET_UNION_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem6982958 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem6982959 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem6982960 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem6982959 t1) (@lem6982958 t1)). Qed.
Lemma lem6982961 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem6982960 t1 t2). Qed.
Lemma lem6982962 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem6982963 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem6982962 t1 t2) (@lem6982961 t1 t2)). Qed.
Lemma lem6982964 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem6982963 t1 t2 t3). Qed.
Lemma lem6982965 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem6982966 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem6982965 t1 t2 t3) (@lem6982964 t1 t2 t3)). Qed.
Lemma lem6982967 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem6982966 t1 t2 t3)). Qed.
Lemma lem6982969 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6982970 {_128167 : Type'} (f : _128167 -> nat) : (term8 _128167 f) = (term9 _128167 f).
Proof. exact (@lem6982969 (term8 _128167 f)). Qed.
Lemma lem6982971 {_128167 : Type'} (f : _128167 -> nat) : (term9 _128167 f) = (term8 _128167 f).
Proof. exact (SYM (@lem6982970 _128167 f)). Qed.
Lemma lem6982972 {_128167 : Type'} (f : _128167 -> nat) (h1 : term10 _128167 f) : term10 _128167 f.
Proof. exact (h1). Qed.
Lemma lem6982973 {_128167 : Type'} : term11 _128167.
Proof. exact (@lem6925097 _128167). Qed.
Lemma lem6982976 {_128167 : Type'} : term12 _128167.
Proof. exact (@lem3196110 _128167). Qed.
Lemma lem6982977 {_126551 : Type'} : term12 _126551.
Proof. exact (@lem3196110 _126551). Qed.
Lemma lem6982981 {_128167 : Type'} : term13 _128167.
Proof. exact (@lem3599924 _128167). Qed.
Lemma lem6982982 {_126551 : Type'} : term13 _126551.
Proof. exact (@lem3599924 _126551). Qed.
Lemma lem6982983 {_128167 : Type'} : term14 _128167.
Proof. exact (@lem3234183 _128167). Qed.
Lemma lem6982984 {_126551 : Type'} : term14 _126551.
Proof. exact (@lem3234183 _126551). Qed.
Lemma lem6982989 {_126551 _128167 : Type'} (f : _128167 -> nat) (h1 : term15 _126551 _128167 f) : term15 _126551 _128167 f.
Proof. exact (h1). Qed.
Lemma lem6982990 {_126551 _128167 : Type'} (f : _128167 -> nat) : term16 _126551 _128167 f.
Proof. exact (fun h0 : term15 _126551 _128167 f => @lem6982989 _126551 _128167 f h0). Qed.
Lemma lem6982991 {_126551 _128167 : Type'} (f : _128167 -> nat) (h1 : term16 _126551 _128167 f) : term16 _126551 _128167 f.
Proof. exact (h1). Qed.
Lemma lem6982992 {_126551 _128167 : Type'} (f : _128167 -> nat) (h1 : term15 _126551 _128167 f) : term15 _126551 _128167 f.
Proof. exact (h1). Qed.
Lemma lem6982993 {_126551 _128167 : Type'} (f : _128167 -> nat) (h1 : term15 _126551 _128167 f) (h2 : term16 _126551 _128167 f) : term15 _126551 _128167 f.
Proof. exact (@lem6982991 _126551 _128167 f h2 (@lem6982992 _126551 _128167 f h1)). Qed.
Lemma lem6982994 {_126551 _128167 : Type'} (f : _128167 -> nat) (h1 : term15 _126551 _128167 f) : term17 _126551 _128167 f.
Proof. exact (fun h0 : term16 _126551 _128167 f => @lem6982993 _126551 _128167 f h1 h0). Qed.
Lemma lem6982995 {_126551 _128167 : Type'} (f : _128167 -> nat) (h1 : term16 _126551 _128167 f) : term16 _126551 _128167 f.
Proof. exact (h1). Qed.
Lemma lem6982996 {_126551 _128167 : Type'} (f : _128167 -> nat) (h1 : term15 _126551 _128167 f) (h2 : term16 _126551 _128167 f) : term15 _126551 _128167 f.
Proof. exact (@lem6982994 _126551 _128167 f h1 (@lem6982995 _126551 _128167 f h2)). Qed.
Lemma lem6982997 {_126551 _128167 : Type'} (f : _128167 -> nat) (h1 : term16 _126551 _128167 f) : term16 _126551 _128167 f.
Proof. exact (fun h0 : term15 _126551 _128167 f => @lem6982996 _126551 _128167 f h0 h1). Qed.
Lemma lem6982998 {_126551 _128167 : Type'} (f : _128167 -> nat) : term18 _126551 _128167 f.
Proof. exact (fun h0 : term16 _126551 _128167 f => @lem6982997 _126551 _128167 f h0). Qed.
Lemma lem6983001 {_126551 _128167 : Type'} (f : _128167 -> nat) : term16 _126551 _128167 f.
Proof. exact (@lem6982998 _126551 _128167 f (@lem6982990 _126551 _128167 f)). Qed.
Lemma lem6983002 {_126551 _128167 : Type'} (f : _128167 -> nat) : term16 _126551 _128167 f.
Proof. exact (@lem6983001 _126551 _128167 f). Qed.
Lemma lem6983136 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6983137 {_128167 : Type'} : (term19 _128167) = (term20 _128167).
Proof. exact (@lem6983136 (term11 _128167)). Qed.
Lemma lem6983156 {_126551 : Type'} : (term21 _126551) = (term21 _126551).
Proof. exact (eq_refl (term21 _126551)). Qed.
Lemma lem6983157 {_126551 _128167 : Type'} : (term22 _126551 _128167) = (term23 _126551 _128167).
Proof. exact (MK_COMB (@lem6983156 _126551) (@lem6983137 _128167)). Qed.
Lemma lem6983160 {_128167 : Type'} : (term24 _128167) = (term24 _128167).
Proof. exact (eq_refl (term24 _128167)). Qed.
Lemma lem6983161 {_126551 _128167 : Type'} : (term25 _126551 _128167) = (term26 _126551 _128167).
Proof. exact (MK_COMB (@lem6983160 _128167) (@lem6983157 _126551 _128167)). Qed.
Lemma lem6983164 {_126551 : Type'} : (term24 _126551) = (term24 _126551).
Proof. exact (eq_refl (term24 _126551)). Qed.
Lemma lem6983165 {_126551 _128167 : Type'} : (term27 _126551 _128167) = (term28 _126551 _128167).
Proof. exact (MK_COMB (@lem6983164 _126551) (@lem6983161 _126551 _128167)). Qed.
Lemma lem6983168 {_128167 : Type'} : (term29 _128167) = (term29 _128167).
Proof. exact (eq_refl (term29 _128167)). Qed.
Lemma lem6983169 {_126551 _128167 : Type'} : (term30 _126551 _128167) = (term31 _126551 _128167).
Proof. exact (MK_COMB (@lem6983168 _128167) (@lem6983165 _126551 _128167)). Qed.
Lemma lem6983172 {_126551 : Type'} : (term29 _126551) = (term29 _126551).
Proof. exact (eq_refl (term29 _126551)). Qed.
Lemma lem6983173 {_126551 _128167 : Type'} : (term32 _126551 _128167) = (term33 _126551 _128167).
Proof. exact (MK_COMB (@lem6983172 _126551) (@lem6983169 _126551 _128167)). Qed.
Lemma lem6983176 {_128167 : Type'} : (term34 _128167) = (term34 _128167).
Proof. exact (eq_refl (term34 _128167)). Qed.
Lemma lem6983177 {_126551 _128167 : Type'} : (term35 _126551 _128167) = (term36 _126551 _128167).
Proof. exact (MK_COMB (@lem6983176 _128167) (@lem6983173 _126551 _128167)). Qed.
Lemma lem6983180 {_126551 : Type'} : (term34 _126551) = (term34 _126551).
Proof. exact (eq_refl (term34 _126551)). Qed.
Lemma lem6983181 {_126551 _128167 : Type'} : (term37 _126551 _128167) = (term38 _126551 _128167).
Proof. exact (MK_COMB (@lem6983180 _126551) (@lem6983177 _126551 _128167)). Qed.
Lemma lem6983184 {_128167 : Type'} (f : _128167 -> nat) : (term39 _128167 f) = (term39 _128167 f).
Proof. exact (eq_refl (term39 _128167 f)). Qed.
Lemma lem6983185 {_126551 _128167 : Type'} (f : _128167 -> nat) : (term15 _126551 _128167 f) = (term40 _126551 _128167 f).
Proof. exact (MK_COMB (@lem6983184 _128167 f) (@lem6983181 _126551 _128167)). Qed.
Lemma lem6983188 {_126551 _128167 : Type'} : (term41 _126551 _128167) = (term42 _126551 _128167).
Proof. exact (fun_ext (fun f : _128167 -> nat => @lem6983185 _126551 _128167 f)). Qed.
Lemma lem6983189 {_128167 : Type'} : (@all (_128167 -> nat)) = (@all (_128167 -> nat)).
Proof. exact (eq_refl (@all (_128167 -> nat))). Qed.
Lemma lem6983198 {_126551 _128167 : Type'} : (term43 _126551 _128167) = (term44 _126551 _128167).
Proof. exact (MK_COMB (@lem6983189 _128167) (@lem6983188 _126551 _128167)). Qed.
Lemma lem6983211 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : (term45 _128167 s t f) = (term45 _128167 s t f).
Proof. exact (eq_refl (term45 _128167 s t f)). Qed.
Lemma lem6983212 {_128167 : Type'} (s : _128167 -> Prop) (f : _128167 -> nat) : (term46 _128167 s f) = (term46 _128167 s f).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6983211 _128167 s t f)). Qed.
Lemma lem6983213 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6983214 {_128167 : Type'} (s : _128167 -> Prop) (f : _128167 -> nat) : (term47 _128167 s f) = (term47 _128167 s f).
Proof. exact (MK_COMB (@lem6983213 _128167) (@lem6983212 _128167 s f)). Qed.
Lemma lem6983215 {_128167 : Type'} (f : _128167 -> nat) : (term48 _128167 f) = (term48 _128167 f).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6983214 _128167 s f)). Qed.
Lemma lem6983216 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6983217 {_128167 : Type'} (f : _128167 -> nat) : (term49 _128167 f) = (term49 _128167 f).
Proof. exact (MK_COMB (@lem6983216 _128167) (@lem6983215 _128167 f)). Qed.
Lemma lem6983218 {_128167 : Type'} : (term50 _128167) = (term50 _128167).
Proof. exact (fun_ext (fun f : _128167 -> nat => @lem6983217 _128167 f)). Qed.
Lemma lem6983219 {_128167 : Type'} : (@all (_128167 -> nat)) = (@all (_128167 -> nat)).
Proof. exact (eq_refl (@all (_128167 -> nat))). Qed.
Lemma lem6983220 {_128167 : Type'} : (term11 _128167) = (term11 _128167).
Proof. exact (MK_COMB (@lem6983219 _128167) (@lem6983218 _128167)). Qed.
Lemma lem6983221 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6983222 {_128167 : Type'} : (term20 _128167) = (term20 _128167).
Proof. exact (MK_COMB (@lem6983221) (@lem6983220 _128167)). Qed.
Lemma lem6983235 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) (f : _126551 -> nat) : (term45 _126551 s t f) = (term45 _126551 s t f).
Proof. exact (eq_refl (term45 _126551 s t f)). Qed.
Lemma lem6983236 {_126551 : Type'} (s : _126551 -> Prop) (f : _126551 -> nat) : (term46 _126551 s f) = (term46 _126551 s f).
Proof. exact (fun_ext (fun t : _126551 -> Prop => @lem6983235 _126551 s t f)). Qed.
Lemma lem6983237 {_126551 : Type'} : (@all (_126551 -> Prop)) = (@all (_126551 -> Prop)).
Proof. exact (eq_refl (@all (_126551 -> Prop))). Qed.
Lemma lem6983238 {_126551 : Type'} (s : _126551 -> Prop) (f : _126551 -> nat) : (term47 _126551 s f) = (term47 _126551 s f).
Proof. exact (MK_COMB (@lem6983237 _126551) (@lem6983236 _126551 s f)). Qed.
Lemma lem6983239 {_126551 : Type'} (f : _126551 -> nat) : (term48 _126551 f) = (term48 _126551 f).
Proof. exact (fun_ext (fun s : _126551 -> Prop => @lem6983238 _126551 s f)). Qed.
Lemma lem6983240 {_126551 : Type'} : (@all (_126551 -> Prop)) = (@all (_126551 -> Prop)).
Proof. exact (eq_refl (@all (_126551 -> Prop))). Qed.
Lemma lem6983241 {_126551 : Type'} (f : _126551 -> nat) : (term49 _126551 f) = (term49 _126551 f).
Proof. exact (MK_COMB (@lem6983240 _126551) (@lem6983239 _126551 f)). Qed.
Lemma lem6983242 {_126551 : Type'} : (term50 _126551) = (term50 _126551).
Proof. exact (fun_ext (fun f : _126551 -> nat => @lem6983241 _126551 f)). Qed.
Lemma lem6983243 {_126551 : Type'} : (@all (_126551 -> nat)) = (@all (_126551 -> nat)).
Proof. exact (eq_refl (@all (_126551 -> nat))). Qed.
Lemma lem6983244 {_126551 : Type'} : (term11 _126551) = (term11 _126551).
Proof. exact (MK_COMB (@lem6983243 _126551) (@lem6983242 _126551)). Qed.
Lemma lem6983245 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6983246 {_126551 : Type'} : (term21 _126551) = (term21 _126551).
Proof. exact (MK_COMB (@lem6983245) (@lem6983244 _126551)). Qed.
Lemma lem6983247 {_126551 _128167 : Type'} : (term23 _126551 _128167) = (term23 _126551 _128167).
Proof. exact (MK_COMB (@lem6983246 _126551) (@lem6983222 _128167)). Qed.
Lemma lem6983252 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : ((@DISJOINT _128167 s t) = ((@INTER _128167 s t) = (@EMPTY _128167))) = ((@DISJOINT _128167 s t) = ((@INTER _128167 s t) = (@EMPTY _128167))).
Proof. exact (eq_refl ((@DISJOINT _128167 s t) = ((@INTER _128167 s t) = (@EMPTY _128167)))). Qed.
Lemma lem6983253 {_128167 : Type'} (s : _128167 -> Prop) : (term51 _128167 s) = (term51 _128167 s).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6983252 _128167 s t)). Qed.
Lemma lem6983254 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6983255 {_128167 : Type'} (s : _128167 -> Prop) : (term52 _128167 s) = (term52 _128167 s).
Proof. exact (MK_COMB (@lem6983254 _128167) (@lem6983253 _128167 s)). Qed.
Lemma lem6983256 {_128167 : Type'} : (term53 _128167) = (term53 _128167).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6983255 _128167 s)). Qed.
Lemma lem6983257 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6983258 {_128167 : Type'} : (term12 _128167) = (term12 _128167).
Proof. exact (MK_COMB (@lem6983257 _128167) (@lem6983256 _128167)). Qed.
Lemma lem6983259 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6983260 {_128167 : Type'} : (term24 _128167) = (term24 _128167).
Proof. exact (MK_COMB (@lem6983259) (@lem6983258 _128167)). Qed.
Lemma lem6983261 {_126551 _128167 : Type'} : (term26 _126551 _128167) = (term26 _126551 _128167).
Proof. exact (MK_COMB (@lem6983260 _128167) (@lem6983247 _126551 _128167)). Qed.
Lemma lem6983266 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) : ((@DISJOINT _126551 s t) = ((@INTER _126551 s t) = (@EMPTY _126551))) = ((@DISJOINT _126551 s t) = ((@INTER _126551 s t) = (@EMPTY _126551))).
Proof. exact (eq_refl ((@DISJOINT _126551 s t) = ((@INTER _126551 s t) = (@EMPTY _126551)))). Qed.
Lemma lem6983267 {_126551 : Type'} (s : _126551 -> Prop) : (term51 _126551 s) = (term51 _126551 s).
Proof. exact (fun_ext (fun t : _126551 -> Prop => @lem6983266 _126551 s t)). Qed.
Lemma lem6983268 {_126551 : Type'} : (@all (_126551 -> Prop)) = (@all (_126551 -> Prop)).
Proof. exact (eq_refl (@all (_126551 -> Prop))). Qed.
Lemma lem6983269 {_126551 : Type'} (s : _126551 -> Prop) : (term52 _126551 s) = (term52 _126551 s).
Proof. exact (MK_COMB (@lem6983268 _126551) (@lem6983267 _126551 s)). Qed.
Lemma lem6983270 {_126551 : Type'} : (term53 _126551) = (term53 _126551).
Proof. exact (fun_ext (fun s : _126551 -> Prop => @lem6983269 _126551 s)). Qed.
Lemma lem6983271 {_126551 : Type'} : (@all (_126551 -> Prop)) = (@all (_126551 -> Prop)).
Proof. exact (eq_refl (@all (_126551 -> Prop))). Qed.
Lemma lem6983272 {_126551 : Type'} : (term12 _126551) = (term12 _126551).
Proof. exact (MK_COMB (@lem6983271 _126551) (@lem6983270 _126551)). Qed.
Lemma lem6983273 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6983274 {_126551 : Type'} : (term24 _126551) = (term24 _126551).
Proof. exact (MK_COMB (@lem6983273) (@lem6983272 _126551)). Qed.
Lemma lem6983275 {_126551 _128167 : Type'} : (term28 _126551 _128167) = (term28 _126551 _128167).
Proof. exact (MK_COMB (@lem6983274 _126551) (@lem6983261 _126551 _128167)). Qed.
Lemma lem6983284 {_128167 : Type'} (t : _128167 -> Prop) (s : _128167 -> Prop) : (term54 _128167 t s) = (term54 _128167 t s).
Proof. exact (eq_refl (term54 _128167 t s)). Qed.
Lemma lem6983285 {_128167 : Type'} (s : _128167 -> Prop) : (term55 _128167 s) = (term55 _128167 s).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6983284 _128167 t s)). Qed.
Lemma lem6983286 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6983287 {_128167 : Type'} (s : _128167 -> Prop) : (term56 _128167 s) = (term56 _128167 s).
Proof. exact (MK_COMB (@lem6983286 _128167) (@lem6983285 _128167 s)). Qed.
Lemma lem6983288 {_128167 : Type'} : (term57 _128167) = (term57 _128167).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6983287 _128167 s)). Qed.
Lemma lem6983289 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6983290 {_128167 : Type'} : (term13 _128167) = (term13 _128167).
Proof. exact (MK_COMB (@lem6983289 _128167) (@lem6983288 _128167)). Qed.
Lemma lem6983291 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6983292 {_128167 : Type'} : (term29 _128167) = (term29 _128167).
Proof. exact (MK_COMB (@lem6983291) (@lem6983290 _128167)). Qed.
Lemma lem6983293 {_126551 _128167 : Type'} : (term31 _126551 _128167) = (term31 _126551 _128167).
Proof. exact (MK_COMB (@lem6983292 _128167) (@lem6983275 _126551 _128167)). Qed.
Lemma lem6983302 {_126551 : Type'} (t : _126551 -> Prop) (s : _126551 -> Prop) : (term54 _126551 t s) = (term54 _126551 t s).
Proof. exact (eq_refl (term54 _126551 t s)). Qed.
Lemma lem6983303 {_126551 : Type'} (s : _126551 -> Prop) : (term55 _126551 s) = (term55 _126551 s).
Proof. exact (fun_ext (fun t : _126551 -> Prop => @lem6983302 _126551 t s)). Qed.
Lemma lem6983304 {_126551 : Type'} : (@all (_126551 -> Prop)) = (@all (_126551 -> Prop)).
Proof. exact (eq_refl (@all (_126551 -> Prop))). Qed.
Lemma lem6983305 {_126551 : Type'} (s : _126551 -> Prop) : (term56 _126551 s) = (term56 _126551 s).
Proof. exact (MK_COMB (@lem6983304 _126551) (@lem6983303 _126551 s)). Qed.
Lemma lem6983306 {_126551 : Type'} : (term57 _126551) = (term57 _126551).
Proof. exact (fun_ext (fun s : _126551 -> Prop => @lem6983305 _126551 s)). Qed.
Lemma lem6983307 {_126551 : Type'} : (@all (_126551 -> Prop)) = (@all (_126551 -> Prop)).
Proof. exact (eq_refl (@all (_126551 -> Prop))). Qed.
Lemma lem6983308 {_126551 : Type'} : (term13 _126551) = (term13 _126551).
Proof. exact (MK_COMB (@lem6983307 _126551) (@lem6983306 _126551)). Qed.
Lemma lem6983309 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6983310 {_126551 : Type'} : (term29 _126551) = (term29 _126551).
Proof. exact (MK_COMB (@lem6983309) (@lem6983308 _126551)). Qed.
Lemma lem6983311 {_126551 _128167 : Type'} : (term33 _126551 _128167) = (term33 _126551 _128167).
Proof. exact (MK_COMB (@lem6983310 _126551) (@lem6983293 _126551 _128167)). Qed.
Lemma lem6983312 {_128167 : Type'} (t : _128167 -> Prop) (s : _128167 -> Prop) : (term58 _128167 t s) = (term58 _128167 t s).
Proof. exact (eq_refl (term58 _128167 t s)). Qed.
Lemma lem6983313 {_128167 : Type'} (s : _128167 -> Prop) : (term59 _128167 s) = (term59 _128167 s).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6983312 _128167 t s)). Qed.
Lemma lem6983314 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6983315 {_128167 : Type'} (s : _128167 -> Prop) : (term60 _128167 s) = (term60 _128167 s).
Proof. exact (MK_COMB (@lem6983314 _128167) (@lem6983313 _128167 s)). Qed.
Lemma lem6983316 {_128167 : Type'} : (term61 _128167) = (term61 _128167).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6983315 _128167 s)). Qed.
Lemma lem6983317 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6983318 {_128167 : Type'} : (term62 _128167) = (term62 _128167).
Proof. exact (MK_COMB (@lem6983317 _128167) (@lem6983316 _128167)). Qed.
Lemma lem6983319 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term63 _128167 s t) = (term63 _128167 s t).
Proof. exact (eq_refl (term63 _128167 s t)). Qed.
Lemma lem6983320 {_128167 : Type'} (s : _128167 -> Prop) : (term64 _128167 s) = (term64 _128167 s).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6983319 _128167 s t)). Qed.
Lemma lem6983321 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6983322 {_128167 : Type'} (s : _128167 -> Prop) : (term65 _128167 s) = (term65 _128167 s).
Proof. exact (MK_COMB (@lem6983321 _128167) (@lem6983320 _128167 s)). Qed.
Lemma lem6983323 {_128167 : Type'} : (term66 _128167) = (term66 _128167).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6983322 _128167 s)). Qed.
Lemma lem6983324 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6983325 {_128167 : Type'} : (term67 _128167) = (term67 _128167).
Proof. exact (MK_COMB (@lem6983324 _128167) (@lem6983323 _128167)). Qed.
Lemma lem6983326 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6983327 {_128167 : Type'} : (term68 _128167) = (term68 _128167).
Proof. exact (MK_COMB (@lem6983326) (@lem6983325 _128167)). Qed.
Lemma lem6983328 {_128167 : Type'} : (term14 _128167) = (term14 _128167).
Proof. exact (MK_COMB (@lem6983327 _128167) (@lem6983318 _128167)). Qed.
Lemma lem6983329 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6983330 {_128167 : Type'} : (term34 _128167) = (term34 _128167).
Proof. exact (MK_COMB (@lem6983329) (@lem6983328 _128167)). Qed.
Lemma lem6983331 {_126551 _128167 : Type'} : (term36 _126551 _128167) = (term36 _126551 _128167).
Proof. exact (MK_COMB (@lem6983330 _128167) (@lem6983311 _126551 _128167)). Qed.
Lemma lem6983332 {_126551 : Type'} (t : _126551 -> Prop) (s : _126551 -> Prop) : (term58 _126551 t s) = (term58 _126551 t s).
Proof. exact (eq_refl (term58 _126551 t s)). Qed.
Lemma lem6983333 {_126551 : Type'} (s : _126551 -> Prop) : (term59 _126551 s) = (term59 _126551 s).
Proof. exact (fun_ext (fun t : _126551 -> Prop => @lem6983332 _126551 t s)). Qed.
Lemma lem6983334 {_126551 : Type'} : (@all (_126551 -> Prop)) = (@all (_126551 -> Prop)).
Proof. exact (eq_refl (@all (_126551 -> Prop))). Qed.
Lemma lem6983335 {_126551 : Type'} (s : _126551 -> Prop) : (term60 _126551 s) = (term60 _126551 s).
Proof. exact (MK_COMB (@lem6983334 _126551) (@lem6983333 _126551 s)). Qed.
Lemma lem6983336 {_126551 : Type'} : (term61 _126551) = (term61 _126551).
Proof. exact (fun_ext (fun s : _126551 -> Prop => @lem6983335 _126551 s)). Qed.
Lemma lem6983337 {_126551 : Type'} : (@all (_126551 -> Prop)) = (@all (_126551 -> Prop)).
Proof. exact (eq_refl (@all (_126551 -> Prop))). Qed.
Lemma lem6983338 {_126551 : Type'} : (term62 _126551) = (term62 _126551).
Proof. exact (MK_COMB (@lem6983337 _126551) (@lem6983336 _126551)). Qed.
Lemma lem6983339 {_126551 : Type'} (s : _126551 -> Prop) (t : _126551 -> Prop) : (term63 _126551 s t) = (term63 _126551 s t).
Proof. exact (eq_refl (term63 _126551 s t)). Qed.
Lemma lem6983340 {_126551 : Type'} (s : _126551 -> Prop) : (term64 _126551 s) = (term64 _126551 s).
Proof. exact (fun_ext (fun t : _126551 -> Prop => @lem6983339 _126551 s t)). Qed.
Lemma lem6983341 {_126551 : Type'} : (@all (_126551 -> Prop)) = (@all (_126551 -> Prop)).
Proof. exact (eq_refl (@all (_126551 -> Prop))). Qed.
Lemma lem6983342 {_126551 : Type'} (s : _126551 -> Prop) : (term65 _126551 s) = (term65 _126551 s).
Proof. exact (MK_COMB (@lem6983341 _126551) (@lem6983340 _126551 s)). Qed.
Lemma lem6983343 {_126551 : Type'} : (term66 _126551) = (term66 _126551).
Proof. exact (fun_ext (fun s : _126551 -> Prop => @lem6983342 _126551 s)). Qed.
Lemma lem6983344 {_126551 : Type'} : (@all (_126551 -> Prop)) = (@all (_126551 -> Prop)).
Proof. exact (eq_refl (@all (_126551 -> Prop))). Qed.
Lemma lem6983345 {_126551 : Type'} : (term67 _126551) = (term67 _126551).
Proof. exact (MK_COMB (@lem6983344 _126551) (@lem6983343 _126551)). Qed.
Lemma lem6983346 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6983347 {_126551 : Type'} : (term68 _126551) = (term68 _126551).
Proof. exact (MK_COMB (@lem6983346) (@lem6983345 _126551)). Qed.
Lemma lem6983348 {_126551 : Type'} : (term14 _126551) = (term14 _126551).
Proof. exact (MK_COMB (@lem6983347 _126551) (@lem6983338 _126551)). Qed.
Lemma lem6983349 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6983350 {_126551 : Type'} : (term34 _126551) = (term34 _126551).
Proof. exact (MK_COMB (@lem6983349) (@lem6983348 _126551)). Qed.
Lemma lem6983351 {_126551 _128167 : Type'} : (term38 _126551 _128167) = (term38 _126551 _128167).
Proof. exact (MK_COMB (@lem6983350 _126551) (@lem6983331 _126551 _128167)). Qed.
Lemma lem6983364 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) : (term69 _128167 s t u f) = (term69 _128167 s t u f).
Proof. exact (eq_refl (term69 _128167 s t u f)). Qed.
Lemma lem6983365 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : (term70 _128167 s t f) = (term70 _128167 s t f).
Proof. exact (fun_ext (fun u : _128167 -> Prop => @lem6983364 _128167 s t u f)). Qed.
Lemma lem6983366 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6983367 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : (term71 _128167 s t f) = (term71 _128167 s t f).
Proof. exact (MK_COMB (@lem6983366 _128167) (@lem6983365 _128167 s t f)). Qed.
Lemma lem6983368 {_128167 : Type'} (s : _128167 -> Prop) (f : _128167 -> nat) : (term72 _128167 s f) = (term72 _128167 s f).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6983367 _128167 s t f)). Qed.
Lemma lem6983369 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6983370 {_128167 : Type'} (s : _128167 -> Prop) (f : _128167 -> nat) : (term73 _128167 s f) = (term73 _128167 s f).
Proof. exact (MK_COMB (@lem6983369 _128167) (@lem6983368 _128167 s f)). Qed.
Lemma lem6983371 {_128167 : Type'} (f : _128167 -> nat) : (term74 _128167 f) = (term74 _128167 f).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6983370 _128167 s f)). Qed.
Lemma lem6983372 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6983373 {_128167 : Type'} (f : _128167 -> nat) : (term8 _128167 f) = (term8 _128167 f).
Proof. exact (MK_COMB (@lem6983372 _128167) (@lem6983371 _128167 f)). Qed.
Lemma lem6983374 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6983375 {_128167 : Type'} (f : _128167 -> nat) : (term10 _128167 f) = (term10 _128167 f).
Proof. exact (MK_COMB (@lem6983374) (@lem6983373 _128167 f)). Qed.
Lemma lem6983376 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6983377 {_128167 : Type'} (f : _128167 -> nat) : (term39 _128167 f) = (term39 _128167 f).
Proof. exact (MK_COMB (@lem6983376) (@lem6983375 _128167 f)). Qed.
Lemma lem6983378 {_126551 _128167 : Type'} (f : _128167 -> nat) : (term40 _126551 _128167 f) = (term40 _126551 _128167 f).
Proof. exact (MK_COMB (@lem6983377 _128167 f) (@lem6983351 _126551 _128167)). Qed.
Lemma lem6983379 {_126551 _128167 : Type'} : (term42 _126551 _128167) = (term42 _126551 _128167).
Proof. exact (fun_ext (fun f : _128167 -> nat => @lem6983378 _126551 _128167 f)). Qed.
Lemma lem6983380 {_128167 : Type'} : (@all (_128167 -> nat)) = (@all (_128167 -> nat)).
Proof. exact (eq_refl (@all (_128167 -> nat))). Qed.
Lemma lem6983381 {_126551 _128167 : Type'} : (term44 _126551 _128167) = (term44 _126551 _128167).
Proof. exact (MK_COMB (@lem6983380 _128167) (@lem6983379 _126551 _128167)). Qed.
Lemma lem6983586 {_126551 _128167 : Type'} : (term43 _126551 _128167) = (term44 _126551 _128167).
Proof. exact (TRANS (@lem6983198 _126551 _128167) (@lem6983381 _126551 _128167)). Qed.
Lemma lem6983587 {_126551 _128167 : Type'} : (term44 _126551 _128167) = (term43 _126551 _128167).
Proof. exact (SYM (@lem6983586 _126551 _128167)). Qed.
Lemma lem6983588 {_128167 : Type'} (f : _128167 -> nat) (h1 : term10 _128167 f) : term10 _128167 f.
Proof. exact (h1). Qed.
Lemma lem6983590 {_128167 : Type'} (h1 : term14 _128167) : term14 _128167.
Proof. exact (h1). Qed.
Lemma lem6983592 {_128167 : Type'} (h1 : term13 _128167) : term13 _128167.
Proof. exact (h1). Qed.
Lemma lem6983594 {_128167 : Type'} (h1 : term12 _128167) : term12 _128167.
Proof. exact (h1). Qed.
Lemma lem6983596 {_128167 : Type'} (h1 : term11 _128167) : term11 _128167.
Proof. exact (h1). Qed.
Lemma lem6983611 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) : (term75 _128167 s t u f) = (term76 _128167 s t u f).
Proof. exact (@lem17362 (term77 _128167 s t u) ((term78 _128167 s t f) = (@nsum _128167 u f))). Qed.
Lemma lem6983612 {_128167 : Type'} (P : type686 _128167) : (term79 _128167 P) = (term80 _128167 P).
Proof. exact (@lem18392 (_128167 -> Prop) P). Qed.
Lemma lem6983613 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : (term81 _128167 s t f) = (term82 _128167 s t f).
Proof. exact (@lem6983612 _128167 (term70 _128167 s t f)). Qed.
Lemma lem6983614 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) : (term83 _128167 s t f u) = (term69 _128167 s t u f).
Proof. exact (eq_refl (term83 _128167 s t f u)). Qed.
Lemma lem6983615 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6983616 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) : (term84 _128167 s t f u) = (term75 _128167 s t u f).
Proof. exact (MK_COMB (@lem6983615) (@lem6983614 _128167 s t u f)). Qed.
Lemma lem6983617 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) : (term84 _128167 s t f u) = (term76 _128167 s t u f).
Proof. exact (TRANS (@lem6983616 _128167 s t u f) (@lem6983611 _128167 s t u f)). Qed.
Lemma lem6983618 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : (term85 _128167 s t f) = (term86 _128167 s t f).
Proof. exact (fun_ext (fun u : _128167 -> Prop => @lem6983617 _128167 s t u f)). Qed.
Lemma lem6983619 {_128167 : Type'} : (@ex (_128167 -> Prop)) = (@ex (_128167 -> Prop)).
Proof. exact (eq_refl (@ex (_128167 -> Prop))). Qed.
Lemma lem6983620 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : (term82 _128167 s t f) = (term87 _128167 s t f).
Proof. exact (MK_COMB (@lem6983619 _128167) (@lem6983618 _128167 s t f)). Qed.
Lemma lem6983621 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : (term81 _128167 s t f) = (term87 _128167 s t f).
Proof. exact (TRANS (@lem6983613 _128167 s t f) (@lem6983620 _128167 s t f)). Qed.
Lemma lem6983622 {_128167 : Type'} (P : type686 _128167) : (term79 _128167 P) = (term80 _128167 P).
Proof. exact (@lem18392 (_128167 -> Prop) P). Qed.
Lemma lem6983623 {_128167 : Type'} (s : _128167 -> Prop) (f : _128167 -> nat) : (term88 _128167 s f) = (term89 _128167 s f).
Proof. exact (@lem6983622 _128167 (term72 _128167 s f)). Qed.
Lemma lem6983624 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : (term90 _128167 s f t) = (term71 _128167 s t f).
Proof. exact (eq_refl (term90 _128167 s f t)). Qed.
Lemma lem6983625 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6983626 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : (term91 _128167 s f t) = (term81 _128167 s t f).
Proof. exact (MK_COMB (@lem6983625) (@lem6983624 _128167 s t f)). Qed.
Lemma lem6983627 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : (term91 _128167 s f t) = (term87 _128167 s t f).
Proof. exact (TRANS (@lem6983626 _128167 s t f) (@lem6983621 _128167 s t f)). Qed.
Lemma lem6983628 {_128167 : Type'} (s : _128167 -> Prop) (f : _128167 -> nat) : (term92 _128167 s f) = (term93 _128167 s f).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6983627 _128167 s t f)). Qed.
Lemma lem6983629 {_128167 : Type'} : (@ex (_128167 -> Prop)) = (@ex (_128167 -> Prop)).
Proof. exact (eq_refl (@ex (_128167 -> Prop))). Qed.
Lemma lem6983630 {_128167 : Type'} (s : _128167 -> Prop) (f : _128167 -> nat) : (term89 _128167 s f) = (term94 _128167 s f).
Proof. exact (MK_COMB (@lem6983629 _128167) (@lem6983628 _128167 s f)). Qed.
Lemma lem6983631 {_128167 : Type'} (s : _128167 -> Prop) (f : _128167 -> nat) : (term88 _128167 s f) = (term94 _128167 s f).
Proof. exact (TRANS (@lem6983623 _128167 s f) (@lem6983630 _128167 s f)). Qed.
Lemma lem6983632 {_128167 : Type'} (P : type686 _128167) : (term79 _128167 P) = (term80 _128167 P).
Proof. exact (@lem18392 (_128167 -> Prop) P). Qed.
Lemma lem6983633 {_128167 : Type'} (f : _128167 -> nat) : (term10 _128167 f) = (term95 _128167 f).
Proof. exact (@lem6983632 _128167 (term74 _128167 f)). Qed.
Lemma lem6983634 {_128167 : Type'} (s : _128167 -> Prop) (f : _128167 -> nat) : (term96 _128167 f s) = (term73 _128167 s f).
Proof. exact (eq_refl (term96 _128167 f s)). Qed.
Lemma lem6983635 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6983636 {_128167 : Type'} (s : _128167 -> Prop) (f : _128167 -> nat) : (term97 _128167 f s) = (term88 _128167 s f).
Proof. exact (MK_COMB (@lem6983635) (@lem6983634 _128167 s f)). Qed.
Lemma lem6983637 {_128167 : Type'} (s : _128167 -> Prop) (f : _128167 -> nat) : (term97 _128167 f s) = (term94 _128167 s f).
Proof. exact (TRANS (@lem6983636 _128167 s f) (@lem6983631 _128167 s f)). Qed.
Lemma lem6983638 {_128167 : Type'} (f : _128167 -> nat) : (term98 _128167 f) = (term99 _128167 f).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6983637 _128167 s f)). Qed.
Lemma lem6983639 {_128167 : Type'} : (@ex (_128167 -> Prop)) = (@ex (_128167 -> Prop)).
Proof. exact (eq_refl (@ex (_128167 -> Prop))). Qed.
Lemma lem6983640 {_128167 : Type'} (f : _128167 -> nat) : (term95 _128167 f) = (term100 _128167 f).
Proof. exact (MK_COMB (@lem6983639 _128167) (@lem6983638 _128167 f)). Qed.
Lemma lem6983701 {_128167 : Type'} (f : _128167 -> nat) : (term10 _128167 f) = (term100 _128167 f).
Proof. exact (TRANS (@lem6983633 _128167 f) (@lem6983640 _128167 f)). Qed.
Lemma lem6983702 {_128167 : Type'} (f : _128167 -> nat) (h1 : term10 _128167 f) : term100 _128167 f.
Proof. exact (EQ_MP (@lem6983701 _128167 f) (@lem6983588 _128167 f h1)). Qed.
Lemma lem6983741 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term63 _128167 s t) = (term63 _128167 s t).
Proof. exact (eq_refl (term63 _128167 s t)). Qed.
Lemma lem6983742 {_128167 : Type'} (s : _128167 -> Prop) : (term64 _128167 s) = (term64 _128167 s).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6983741 _128167 s t)). Qed.
Lemma lem6983743 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6983744 {_128167 : Type'} (s : _128167 -> Prop) : (term65 _128167 s) = (term65 _128167 s).
Proof. exact (MK_COMB (@lem6983743 _128167) (@lem6983742 _128167 s)). Qed.
Lemma lem6983745 {_128167 : Type'} : (term66 _128167) = (term66 _128167).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6983744 _128167 s)). Qed.
Lemma lem6983746 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6983747 {_128167 : Type'} : (term67 _128167) = (term67 _128167).
Proof. exact (MK_COMB (@lem6983746 _128167) (@lem6983745 _128167)). Qed.
Lemma lem6983748 {_128167 : Type'} (t : _128167 -> Prop) (s : _128167 -> Prop) : (term58 _128167 t s) = (term58 _128167 t s).
Proof. exact (eq_refl (term58 _128167 t s)). Qed.
Lemma lem6983749 {_128167 : Type'} (s : _128167 -> Prop) : (term59 _128167 s) = (term59 _128167 s).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6983748 _128167 t s)). Qed.
Lemma lem6983750 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6983751 {_128167 : Type'} (s : _128167 -> Prop) : (term60 _128167 s) = (term60 _128167 s).
Proof. exact (MK_COMB (@lem6983750 _128167) (@lem6983749 _128167 s)). Qed.
Lemma lem6983752 {_128167 : Type'} : (term61 _128167) = (term61 _128167).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6983751 _128167 s)). Qed.
Lemma lem6983753 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6983754 {_128167 : Type'} : (term62 _128167) = (term62 _128167).
Proof. exact (MK_COMB (@lem6983753 _128167) (@lem6983752 _128167)). Qed.
Lemma lem6983755 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6983756 {_128167 : Type'} : (term68 _128167) = (term68 _128167).
Proof. exact (MK_COMB (@lem6983755) (@lem6983747 _128167)). Qed.
Lemma lem6983777 {_128167 : Type'} : (term14 _128167) = (term14 _128167).
Proof. exact (MK_COMB (@lem6983756 _128167) (@lem6983754 _128167)). Qed.
Lemma lem6983778 {_128167 : Type'} (h1 : term14 _128167) : term14 _128167.
Proof. exact (EQ_MP (@lem6983777 _128167) (@lem6983590 _128167 h1)). Qed.
Lemma lem6983939 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term101 _128167 s t) = (term102 _128167 s t).
Proof. exact (@lem17045 (@FINITE _128167 t) (@SUBSET _128167 s t)). Qed.
Lemma lem6983940 {_128167 : Type'} (s : _128167 -> Prop) : (@FINITE _128167 s) = (@FINITE _128167 s).
Proof. exact (eq_refl (@FINITE _128167 s)). Qed.
Lemma lem6983941 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6983942 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term103 _128167 s t) = (term104 _128167 s t).
Proof. exact (MK_COMB (@lem6983941) (@lem6983939 _128167 s t)). Qed.
Lemma lem6983943 {_128167 : Type'} (t : _128167 -> Prop) (s : _128167 -> Prop) : (term105 _128167 t s) = (term106 _128167 t s).
Proof. exact (MK_COMB (@lem6983942 _128167 s t) (@lem6983940 _128167 s)). Qed.
Lemma lem6983944 {_128167 : Type'} (t : _128167 -> Prop) (s : _128167 -> Prop) : (term54 _128167 t s) = (term105 _128167 t s).
Proof. exact (@lem17265 (term107 _128167 s t) (@FINITE _128167 s)). Qed.
Lemma lem6983945 {_128167 : Type'} (t : _128167 -> Prop) (s : _128167 -> Prop) : (term54 _128167 t s) = (term106 _128167 t s).
Proof. exact (TRANS (@lem6983944 _128167 t s) (@lem6983943 _128167 t s)). Qed.
Lemma lem6983946 {_128167 : Type'} (s : _128167 -> Prop) : (term55 _128167 s) = (term108 _128167 s).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6983945 _128167 t s)). Qed.
Lemma lem6983947 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6983948 {_128167 : Type'} (s : _128167 -> Prop) : (term56 _128167 s) = (term109 _128167 s).
Proof. exact (MK_COMB (@lem6983947 _128167) (@lem6983946 _128167 s)). Qed.
Lemma lem6983949 {_128167 : Type'} : (term57 _128167) = (term110 _128167).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6983948 _128167 s)). Qed.
Lemma lem6983950 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6983951 {_128167 : Type'} : (term13 _128167) = (term111 _128167).
Proof. exact (MK_COMB (@lem6983950 _128167) (@lem6983949 _128167)). Qed.
Lemma lem6983977 {A : Type'} (P : A -> Prop) (Q : Prop) : (term112 A P Q) = (term113 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem6983978 {_128167 : Type'} (P : type686 _128167) (Q : Prop) : (term114 _128167 P Q) = (term115 _128167 P Q).
Proof. exact (@lem6983977 (_128167 -> Prop) P Q). Qed.
Lemma lem6983979 {_128167 : Type'} (s : _128167 -> Prop) : (term116 _128167 s) = (term117 _128167 s).
Proof. exact (@lem6983978 _128167 (term118 _128167 s) (@FINITE _128167 s)). Qed.
Lemma lem6983980 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term119 _128167 s t) = (term102 _128167 s t).
Proof. exact (eq_refl (term119 _128167 s t)). Qed.
Lemma lem6983981 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6983982 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term120 _128167 s t) = (term104 _128167 s t).
Proof. exact (MK_COMB (@lem6983981) (@lem6983980 _128167 s t)). Qed.
Lemma lem6983983 {_128167 : Type'} (s : _128167 -> Prop) : (@FINITE _128167 s) = (@FINITE _128167 s).
Proof. exact (eq_refl (@FINITE _128167 s)). Qed.
Lemma lem6983984 {_128167 : Type'} (t : _128167 -> Prop) (s : _128167 -> Prop) : (term121 _128167 t s) = (term106 _128167 t s).
Proof. exact (MK_COMB (@lem6983982 _128167 s t) (@lem6983983 _128167 s)). Qed.
Lemma lem6983985 {_128167 : Type'} (s : _128167 -> Prop) : (term122 _128167 s) = (term108 _128167 s).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6983984 _128167 t s)). Qed.
Lemma lem6983986 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6983987 {_128167 : Type'} (s : _128167 -> Prop) : (term116 _128167 s) = (term109 _128167 s).
Proof. exact (MK_COMB (@lem6983986 _128167) (@lem6983985 _128167 s)). Qed.
Lemma lem6983988 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6983989 {_128167 : Type'} (s : _128167 -> Prop) : (term123 _128167 s) = (term124 _128167 s).
Proof. exact (MK_COMB (@lem6983988) (@lem6983987 _128167 s)). Qed.
Lemma lem6983990 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term119 _128167 s t) = (term102 _128167 s t).
Proof. exact (eq_refl (term119 _128167 s t)). Qed.
Lemma lem6983991 {_128167 : Type'} (s : _128167 -> Prop) : (term125 _128167 s) = (term118 _128167 s).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6983990 _128167 s t)). Qed.
Lemma lem6983992 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6983993 {_128167 : Type'} (s : _128167 -> Prop) : (term126 _128167 s) = (term127 _128167 s).
Proof. exact (MK_COMB (@lem6983992 _128167) (@lem6983991 _128167 s)). Qed.
Lemma lem6983994 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6983995 {_128167 : Type'} (s : _128167 -> Prop) : (term128 _128167 s) = (term129 _128167 s).
Proof. exact (MK_COMB (@lem6983994) (@lem6983993 _128167 s)). Qed.
Lemma lem6983996 {_128167 : Type'} (s : _128167 -> Prop) : (@FINITE _128167 s) = (@FINITE _128167 s).
Proof. exact (eq_refl (@FINITE _128167 s)). Qed.
Lemma lem6983997 {_128167 : Type'} (s : _128167 -> Prop) : (term117 _128167 s) = (term130 _128167 s).
Proof. exact (MK_COMB (@lem6983995 _128167 s) (@lem6983996 _128167 s)). Qed.
Lemma lem6983998 {_128167 : Type'} (s : _128167 -> Prop) : ((term116 _128167 s) = (term117 _128167 s)) = ((term109 _128167 s) = (term130 _128167 s)).
Proof. exact (MK_COMB (@lem6983989 _128167 s) (@lem6983997 _128167 s)). Qed.
Lemma lem6983999 {_128167 : Type'} (s : _128167 -> Prop) : (term109 _128167 s) = (term130 _128167 s).
Proof. exact (EQ_MP (@lem6983998 _128167 s) (@lem6983979 _128167 s)). Qed.
Lemma lem6984048 {_128167 : Type'} : (term110 _128167) = (term131 _128167).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6983999 _128167 s)). Qed.
Lemma lem6984049 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6984084 {_128167 : Type'} : (term111 _128167) = (term132 _128167).
Proof. exact (MK_COMB (@lem6984049 _128167) (@lem6984048 _128167)). Qed.
Lemma lem6984085 {_128167 : Type'} : (term13 _128167) = (term132 _128167).
Proof. exact (TRANS (@lem6983951 _128167) (@lem6984084 _128167)). Qed.
Lemma lem6984086 {_128167 : Type'} (h1 : term13 _128167) : term132 _128167.
Proof. exact (EQ_MP (@lem6984085 _128167) (@lem6983592 _128167 h1)). Qed.
Lemma lem6984388 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : ((@DISJOINT _128167 s t) = ((@INTER _128167 s t) = (@EMPTY _128167))) = (term133 _128167 s t).
Proof. exact (@lem17784 (@DISJOINT _128167 s t) ((@INTER _128167 s t) = (@EMPTY _128167))). Qed.
Lemma lem6984389 {_128167 : Type'} (s : _128167 -> Prop) : (term51 _128167 s) = (term134 _128167 s).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6984388 _128167 s t)). Qed.
Lemma lem6984390 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6984391 {_128167 : Type'} (s : _128167 -> Prop) : (term52 _128167 s) = (term135 _128167 s).
Proof. exact (MK_COMB (@lem6984390 _128167) (@lem6984389 _128167 s)). Qed.
Lemma lem6984392 {_128167 : Type'} : (term53 _128167) = (term136 _128167).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6984391 _128167 s)). Qed.
Lemma lem6984393 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6984394 {_128167 : Type'} : (term12 _128167) = (term137 _128167).
Proof. exact (MK_COMB (@lem6984393 _128167) (@lem6984392 _128167)). Qed.
Lemma lem6984400 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term138 A P Q) = (term139 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6984401 {_128167 : Type'} (P : type686 _128167) (Q : type686 _128167) : (term140 _128167 P Q) = (term141 _128167 P Q).
Proof. exact (@lem6984400 (_128167 -> Prop) P Q). Qed.
Lemma lem6984402 {_128167 : Type'} (s : _128167 -> Prop) : (term142 _128167 s) = (term143 _128167 s).
Proof. exact (@lem6984401 _128167 (term144 _128167 s) (term145 _128167 s)). Qed.
Lemma lem6984403 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term146 _128167 s t) = (term147 _128167 s t).
Proof. exact (eq_refl (term146 _128167 s t)). Qed.
Lemma lem6984404 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6984405 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term148 _128167 s t) = (term149 _128167 s t).
Proof. exact (MK_COMB (@lem6984404) (@lem6984403 _128167 s t)). Qed.
Lemma lem6984406 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term150 _128167 s t) = (term151 _128167 s t).
Proof. exact (eq_refl (term150 _128167 s t)). Qed.
Lemma lem6984407 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term152 _128167 s t) = (term133 _128167 s t).
Proof. exact (MK_COMB (@lem6984405 _128167 s t) (@lem6984406 _128167 s t)). Qed.
Lemma lem6984408 {_128167 : Type'} (s : _128167 -> Prop) : (term153 _128167 s) = (term134 _128167 s).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6984407 _128167 s t)). Qed.
Lemma lem6984409 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6984410 {_128167 : Type'} (s : _128167 -> Prop) : (term142 _128167 s) = (term135 _128167 s).
Proof. exact (MK_COMB (@lem6984409 _128167) (@lem6984408 _128167 s)). Qed.
Lemma lem6984411 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6984412 {_128167 : Type'} (s : _128167 -> Prop) : (term154 _128167 s) = (term155 _128167 s).
Proof. exact (MK_COMB (@lem6984411) (@lem6984410 _128167 s)). Qed.
Lemma lem6984413 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term146 _128167 s t) = (term147 _128167 s t).
Proof. exact (eq_refl (term146 _128167 s t)). Qed.
Lemma lem6984414 {_128167 : Type'} (s : _128167 -> Prop) : (term156 _128167 s) = (term144 _128167 s).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6984413 _128167 s t)). Qed.
Lemma lem6984415 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6984416 {_128167 : Type'} (s : _128167 -> Prop) : (term157 _128167 s) = (term158 _128167 s).
Proof. exact (MK_COMB (@lem6984415 _128167) (@lem6984414 _128167 s)). Qed.
Lemma lem6984417 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6984418 {_128167 : Type'} (s : _128167 -> Prop) : (term159 _128167 s) = (term160 _128167 s).
Proof. exact (MK_COMB (@lem6984417) (@lem6984416 _128167 s)). Qed.
Lemma lem6984419 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term150 _128167 s t) = (term151 _128167 s t).
Proof. exact (eq_refl (term150 _128167 s t)). Qed.
Lemma lem6984420 {_128167 : Type'} (s : _128167 -> Prop) : (term161 _128167 s) = (term145 _128167 s).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6984419 _128167 s t)). Qed.
Lemma lem6984421 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6984422 {_128167 : Type'} (s : _128167 -> Prop) : (term162 _128167 s) = (term163 _128167 s).
Proof. exact (MK_COMB (@lem6984421 _128167) (@lem6984420 _128167 s)). Qed.
Lemma lem6984423 {_128167 : Type'} (s : _128167 -> Prop) : (term143 _128167 s) = (term164 _128167 s).
Proof. exact (MK_COMB (@lem6984418 _128167 s) (@lem6984422 _128167 s)). Qed.
Lemma lem6984424 {_128167 : Type'} (s : _128167 -> Prop) : ((term142 _128167 s) = (term143 _128167 s)) = ((term135 _128167 s) = (term164 _128167 s)).
Proof. exact (MK_COMB (@lem6984412 _128167 s) (@lem6984423 _128167 s)). Qed.
Lemma lem6984425 {_128167 : Type'} (s : _128167 -> Prop) : (term135 _128167 s) = (term164 _128167 s).
Proof. exact (EQ_MP (@lem6984424 _128167 s) (@lem6984402 _128167 s)). Qed.
Lemma lem6984522 {_128167 : Type'} : (term136 _128167) = (term165 _128167).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6984425 _128167 s)). Qed.
Lemma lem6984523 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6984524 {_128167 : Type'} : (term137 _128167) = (term166 _128167).
Proof. exact (MK_COMB (@lem6984523 _128167) (@lem6984522 _128167)). Qed.
Lemma lem6984526 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term138 A P Q) = (term139 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6984527 {_128167 : Type'} (P : type686 _128167) (Q : type686 _128167) : (term140 _128167 P Q) = (term141 _128167 P Q).
Proof. exact (@lem6984526 (_128167 -> Prop) P Q). Qed.
Lemma lem6984528 {_128167 : Type'} : (term167 _128167) = (term168 _128167).
Proof. exact (@lem6984527 _128167 (term169 _128167) (term170 _128167)). Qed.
Lemma lem6984529 {_128167 : Type'} (s : _128167 -> Prop) : (term171 _128167 s) = (term158 _128167 s).
Proof. exact (eq_refl (term171 _128167 s)). Qed.
Lemma lem6984530 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6984531 {_128167 : Type'} (s : _128167 -> Prop) : (term172 _128167 s) = (term160 _128167 s).
Proof. exact (MK_COMB (@lem6984530) (@lem6984529 _128167 s)). Qed.
Lemma lem6984532 {_128167 : Type'} (s : _128167 -> Prop) : (term173 _128167 s) = (term163 _128167 s).
Proof. exact (eq_refl (term173 _128167 s)). Qed.
Lemma lem6984533 {_128167 : Type'} (s : _128167 -> Prop) : (term174 _128167 s) = (term164 _128167 s).
Proof. exact (MK_COMB (@lem6984531 _128167 s) (@lem6984532 _128167 s)). Qed.
Lemma lem6984534 {_128167 : Type'} : (term175 _128167) = (term165 _128167).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6984533 _128167 s)). Qed.
Lemma lem6984535 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6984536 {_128167 : Type'} : (term167 _128167) = (term166 _128167).
Proof. exact (MK_COMB (@lem6984535 _128167) (@lem6984534 _128167)). Qed.
Lemma lem6984537 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6984538 {_128167 : Type'} : (term176 _128167) = (term177 _128167).
Proof. exact (MK_COMB (@lem6984537) (@lem6984536 _128167)). Qed.
Lemma lem6984539 {_128167 : Type'} (s : _128167 -> Prop) : (term171 _128167 s) = (term158 _128167 s).
Proof. exact (eq_refl (term171 _128167 s)). Qed.
Lemma lem6984540 {_128167 : Type'} : (term178 _128167) = (term169 _128167).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6984539 _128167 s)). Qed.
Lemma lem6984541 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6984542 {_128167 : Type'} : (term179 _128167) = (term180 _128167).
Proof. exact (MK_COMB (@lem6984541 _128167) (@lem6984540 _128167)). Qed.
Lemma lem6984543 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6984544 {_128167 : Type'} : (term181 _128167) = (term182 _128167).
Proof. exact (MK_COMB (@lem6984543) (@lem6984542 _128167)). Qed.
Lemma lem6984545 {_128167 : Type'} (s : _128167 -> Prop) : (term173 _128167 s) = (term163 _128167 s).
Proof. exact (eq_refl (term173 _128167 s)). Qed.
Lemma lem6984546 {_128167 : Type'} : (term183 _128167) = (term170 _128167).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6984545 _128167 s)). Qed.
Lemma lem6984547 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6984548 {_128167 : Type'} : (term184 _128167) = (term185 _128167).
Proof. exact (MK_COMB (@lem6984547 _128167) (@lem6984546 _128167)). Qed.
Lemma lem6984549 {_128167 : Type'} : (term168 _128167) = (term186 _128167).
Proof. exact (MK_COMB (@lem6984544 _128167) (@lem6984548 _128167)). Qed.
Lemma lem6984550 {_128167 : Type'} : ((term167 _128167) = (term168 _128167)) = ((term166 _128167) = (term186 _128167)).
Proof. exact (MK_COMB (@lem6984538 _128167) (@lem6984549 _128167)). Qed.
Lemma lem6984551 {_128167 : Type'} : (term166 _128167) = (term186 _128167).
Proof. exact (EQ_MP (@lem6984550 _128167) (@lem6984528 _128167)). Qed.
Lemma lem6984658 {_128167 : Type'} : (term137 _128167) = (term186 _128167).
Proof. exact (TRANS (@lem6984524 _128167) (@lem6984551 _128167)). Qed.
Lemma lem6984659 {_128167 : Type'} : (term12 _128167) = (term186 _128167).
Proof. exact (TRANS (@lem6984394 _128167) (@lem6984658 _128167)). Qed.
Lemma lem6984660 {_128167 : Type'} (h1 : term12 _128167) : term186 _128167.
Proof. exact (EQ_MP (@lem6984659 _128167) (@lem6983594 _128167 h1)). Qed.
Lemma lem6984757 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term187 _128167 s t) = (term188 _128167 s t).
Proof. exact (@lem17045 (@FINITE _128167 t) (@DISJOINT _128167 s t)). Qed.
Lemma lem6984759 {_128167 : Type'} (s : _128167 -> Prop) : (term189 _128167 s) = (term189 _128167 s).
Proof. exact (eq_refl (term189 _128167 s)). Qed.
Lemma lem6984760 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term190 _128167 s t) = (term191 _128167 s t).
Proof. exact (MK_COMB (@lem6984759 _128167 s) (@lem6984757 _128167 s t)). Qed.
Lemma lem6984761 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term192 _128167 s t) = (term190 _128167 s t).
Proof. exact (@lem17045 (@FINITE _128167 s) (term193 _128167 s t)). Qed.
Lemma lem6984762 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term192 _128167 s t) = (term191 _128167 s t).
Proof. exact (TRANS (@lem6984761 _128167 s t) (@lem6984760 _128167 s t)). Qed.
Lemma lem6984763 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : ((term194 _128167 s t f) = (term78 _128167 s t f)) = ((term194 _128167 s t f) = (term78 _128167 s t f)).
Proof. exact (eq_refl ((term194 _128167 s t f) = (term78 _128167 s t f))). Qed.
Lemma lem6984764 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6984765 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term195 _128167 s t) = (term196 _128167 s t).
Proof. exact (MK_COMB (@lem6984764) (@lem6984762 _128167 s t)). Qed.
Lemma lem6984766 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : (term197 _128167 s t f) = (term198 _128167 s t f).
Proof. exact (MK_COMB (@lem6984765 _128167 s t) (@lem6984763 _128167 s t f)). Qed.
Lemma lem6984767 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : (term45 _128167 s t f) = (term197 _128167 s t f).
Proof. exact (@lem17265 (term199 _128167 s t) ((term194 _128167 s t f) = (term78 _128167 s t f))). Qed.
Lemma lem6984768 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : (term45 _128167 s t f) = (term198 _128167 s t f).
Proof. exact (TRANS (@lem6984767 _128167 s t f) (@lem6984766 _128167 s t f)). Qed.
Lemma lem6984769 {_128167 : Type'} (s : _128167 -> Prop) (f : _128167 -> nat) : (term46 _128167 s f) = (term200 _128167 s f).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6984768 _128167 s t f)). Qed.
Lemma lem6984770 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6984771 {_128167 : Type'} (s : _128167 -> Prop) (f : _128167 -> nat) : (term47 _128167 s f) = (term201 _128167 s f).
Proof. exact (MK_COMB (@lem6984770 _128167) (@lem6984769 _128167 s f)). Qed.
Lemma lem6984772 {_128167 : Type'} (f : _128167 -> nat) : (term48 _128167 f) = (term202 _128167 f).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6984771 _128167 s f)). Qed.
Lemma lem6984773 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6984774 {_128167 : Type'} (f : _128167 -> nat) : (term49 _128167 f) = (term203 _128167 f).
Proof. exact (MK_COMB (@lem6984773 _128167) (@lem6984772 _128167 f)). Qed.
Lemma lem6984775 {_128167 : Type'} : (term50 _128167) = (term204 _128167).
Proof. exact (fun_ext (fun f : _128167 -> nat => @lem6984774 _128167 f)). Qed.
Lemma lem6984776 {_128167 : Type'} : (@all (_128167 -> nat)) = (@all (_128167 -> nat)).
Proof. exact (eq_refl (@all (_128167 -> nat))). Qed.
Lemma lem6984837 {_128167 : Type'} : (term11 _128167) = (term205 _128167).
Proof. exact (MK_COMB (@lem6984776 _128167) (@lem6984775 _128167)). Qed.
Lemma lem6984838 {_128167 : Type'} (h1 : term11 _128167) : term205 _128167.
Proof. exact (EQ_MP (@lem6984837 _128167) (@lem6983596 _128167 h1)). Qed.
Lemma lem6984839 {_128167 : Type'} (s : _128167 -> Prop) (f : _128167 -> nat) (h1 : term94 _128167 s f) : term94 _128167 s f.
Proof. exact (h1). Qed.
Lemma lem6984840 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) (h1 : term87 _128167 s t f) : term87 _128167 s t f.
Proof. exact (h1). Qed.
Lemma lem6984884 {_128167 : Type'} (t : _128167 -> Prop) (s : _128167 -> Prop) : (term58 _128167 t s) = (term58 _128167 t s).
Proof. exact (eq_refl (term58 _128167 t s)). Qed.
Lemma lem6984885 {_128167 : Type'} (s : _128167 -> Prop) : (term59 _128167 s) = (term59 _128167 s).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6984884 _128167 t s)). Qed.
Lemma lem6984886 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6984887 {_128167 : Type'} (s : _128167 -> Prop) : (term60 _128167 s) = (term60 _128167 s).
Proof. exact (MK_COMB (@lem6984886 _128167) (@lem6984885 _128167 s)). Qed.
Lemma lem6984888 {_128167 : Type'} : (term61 _128167) = (term61 _128167).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6984887 _128167 s)). Qed.
Lemma lem6984889 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6984890 {_128167 : Type'} : (term62 _128167) = (term62 _128167).
Proof. exact (MK_COMB (@lem6984889 _128167) (@lem6984888 _128167)). Qed.
Lemma lem6984899 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term63 _128167 s t) = (term63 _128167 s t).
Proof. exact (eq_refl (term63 _128167 s t)). Qed.
Lemma lem6984900 {_128167 : Type'} (s : _128167 -> Prop) : (term64 _128167 s) = (term64 _128167 s).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6984899 _128167 s t)). Qed.
Lemma lem6984901 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6984902 {_128167 : Type'} (s : _128167 -> Prop) : (term65 _128167 s) = (term65 _128167 s).
Proof. exact (MK_COMB (@lem6984901 _128167) (@lem6984900 _128167 s)). Qed.
Lemma lem6984903 {_128167 : Type'} : (term66 _128167) = (term66 _128167).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6984902 _128167 s)). Qed.
Lemma lem6984904 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6984905 {_128167 : Type'} : (term67 _128167) = (term67 _128167).
Proof. exact (MK_COMB (@lem6984904 _128167) (@lem6984903 _128167)). Qed.
Lemma lem6984906 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6984907 {_128167 : Type'} : (term68 _128167) = (term68 _128167).
Proof. exact (MK_COMB (@lem6984906) (@lem6984905 _128167)). Qed.
Lemma lem6984908 {_128167 : Type'} : (term14 _128167) = (term14 _128167).
Proof. exact (MK_COMB (@lem6984907 _128167) (@lem6984890 _128167)). Qed.
Lemma lem6984909 {_128167 : Type'} (h1 : term14 _128167) : term14 _128167.
Proof. exact (EQ_MP (@lem6984908 _128167) (@lem6983778 _128167 h1)). Qed.
Lemma lem6984940 {_128167 : Type'} (s : _128167 -> Prop) : (@FINITE _128167 s) = (@FINITE _128167 s).
Proof. exact (eq_refl (@FINITE _128167 s)). Qed.
Lemma lem6984955 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term102 _128167 s t) = (term102 _128167 s t).
Proof. exact (eq_refl (term102 _128167 s t)). Qed.
Lemma lem6984956 {_128167 : Type'} (s : _128167 -> Prop) : (term118 _128167 s) = (term118 _128167 s).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6984955 _128167 s t)). Qed.
Lemma lem6984957 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6984958 {_128167 : Type'} (s : _128167 -> Prop) : (term127 _128167 s) = (term127 _128167 s).
Proof. exact (MK_COMB (@lem6984957 _128167) (@lem6984956 _128167 s)). Qed.
Lemma lem6984959 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6984960 {_128167 : Type'} (s : _128167 -> Prop) : (term129 _128167 s) = (term129 _128167 s).
Proof. exact (MK_COMB (@lem6984959) (@lem6984958 _128167 s)). Qed.
Lemma lem6984961 {_128167 : Type'} (s : _128167 -> Prop) : (term130 _128167 s) = (term130 _128167 s).
Proof. exact (MK_COMB (@lem6984960 _128167 s) (@lem6984940 _128167 s)). Qed.
Lemma lem6984962 {_128167 : Type'} : (term131 _128167) = (term131 _128167).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6984961 _128167 s)). Qed.
Lemma lem6984963 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6984964 {_128167 : Type'} : (term132 _128167) = (term132 _128167).
Proof. exact (MK_COMB (@lem6984963 _128167) (@lem6984962 _128167)). Qed.
Lemma lem6984965 {_128167 : Type'} (h1 : term13 _128167) : term132 _128167.
Proof. exact (EQ_MP (@lem6984964 _128167) (@lem6984086 _128167 h1)). Qed.
Lemma lem6985038 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term151 _128167 s t) = (term151 _128167 s t).
Proof. exact (eq_refl (term151 _128167 s t)). Qed.
Lemma lem6985039 {_128167 : Type'} (s : _128167 -> Prop) : (term145 _128167 s) = (term145 _128167 s).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6985038 _128167 s t)). Qed.
Lemma lem6985040 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6985041 {_128167 : Type'} (s : _128167 -> Prop) : (term163 _128167 s) = (term163 _128167 s).
Proof. exact (MK_COMB (@lem6985040 _128167) (@lem6985039 _128167 s)). Qed.
Lemma lem6985042 {_128167 : Type'} : (term170 _128167) = (term170 _128167).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6985041 _128167 s)). Qed.
Lemma lem6985043 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6985044 {_128167 : Type'} : (term185 _128167) = (term185 _128167).
Proof. exact (MK_COMB (@lem6985043 _128167) (@lem6985042 _128167)). Qed.
Lemma lem6985063 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term147 _128167 s t) = (term147 _128167 s t).
Proof. exact (eq_refl (term147 _128167 s t)). Qed.
Lemma lem6985064 {_128167 : Type'} (s : _128167 -> Prop) : (term144 _128167 s) = (term144 _128167 s).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6985063 _128167 s t)). Qed.
Lemma lem6985065 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6985066 {_128167 : Type'} (s : _128167 -> Prop) : (term158 _128167 s) = (term158 _128167 s).
Proof. exact (MK_COMB (@lem6985065 _128167) (@lem6985064 _128167 s)). Qed.
Lemma lem6985067 {_128167 : Type'} : (term169 _128167) = (term169 _128167).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6985066 _128167 s)). Qed.
Lemma lem6985068 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6985069 {_128167 : Type'} : (term180 _128167) = (term180 _128167).
Proof. exact (MK_COMB (@lem6985068 _128167) (@lem6985067 _128167)). Qed.
Lemma lem6985070 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6985071 {_128167 : Type'} : (term182 _128167) = (term182 _128167).
Proof. exact (MK_COMB (@lem6985070) (@lem6985069 _128167)). Qed.
Lemma lem6985072 {_128167 : Type'} : (term186 _128167) = (term186 _128167).
Proof. exact (MK_COMB (@lem6985071 _128167) (@lem6985044 _128167)). Qed.
Lemma lem6985073 {_128167 : Type'} (h1 : term12 _128167) : term186 _128167.
Proof. exact (EQ_MP (@lem6985072 _128167) (@lem6984660 _128167 h1)). Qed.
Lemma lem6985185 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : (term198 _128167 s t f) = (term198 _128167 s t f).
Proof. exact (eq_refl (term198 _128167 s t f)). Qed.
Lemma lem6985186 {_128167 : Type'} (s : _128167 -> Prop) (f : _128167 -> nat) : (term200 _128167 s f) = (term200 _128167 s f).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6985185 _128167 s t f)). Qed.
Lemma lem6985187 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6985188 {_128167 : Type'} (s : _128167 -> Prop) (f : _128167 -> nat) : (term201 _128167 s f) = (term201 _128167 s f).
Proof. exact (MK_COMB (@lem6985187 _128167) (@lem6985186 _128167 s f)). Qed.
Lemma lem6985189 {_128167 : Type'} (f : _128167 -> nat) : (term202 _128167 f) = (term202 _128167 f).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6985188 _128167 s f)). Qed.
Lemma lem6985190 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6985191 {_128167 : Type'} (f : _128167 -> nat) : (term203 _128167 f) = (term203 _128167 f).
Proof. exact (MK_COMB (@lem6985190 _128167) (@lem6985189 _128167 f)). Qed.
Lemma lem6985192 {_128167 : Type'} : (term204 _128167) = (term204 _128167).
Proof. exact (fun_ext (fun f : _128167 -> nat => @lem6985191 _128167 f)). Qed.
Lemma lem6985193 {_128167 : Type'} : (@all (_128167 -> nat)) = (@all (_128167 -> nat)).
Proof. exact (eq_refl (@all (_128167 -> nat))). Qed.
Lemma lem6985194 {_128167 : Type'} : (term205 _128167) = (term205 _128167).
Proof. exact (MK_COMB (@lem6985193 _128167) (@lem6985192 _128167)). Qed.
Lemma lem6985195 {_128167 : Type'} (h1 : term11 _128167) : term205 _128167.
Proof. exact (EQ_MP (@lem6985194 _128167) (@lem6984838 _128167 h1)). Qed.
Lemma lem6985249 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term76 _128167 s t u f) : term76 _128167 s t u f.
Proof. exact (h1). Qed.
Lemma lem6985251 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term76 _128167 s t u f) : term77 _128167 s t u.
Proof. exact (proj1 (@lem6985249 _128167 s t u f h1)). Qed.
Lemma lem6985252 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term76 _128167 s t u f) : term206 _128167 s t u.
Proof. exact (proj2 (@lem6985251 _128167 s t u f h1)). Qed.
Lemma lem6985257 {_128167 : Type'} (h1 : term12 _128167) : term180 _128167.
Proof. exact (proj1 (@lem6985073 _128167 h1)). Qed.
Lemma lem6985260 {_128167 : Type'} (h1 : term14 _128167) : term62 _128167.
Proof. exact (proj2 (@lem6984909 _128167 h1)). Qed.
Lemma lem6985261 {_128167 : Type'} (h1 : term14 _128167) : term67 _128167.
Proof. exact (proj1 (@lem6984909 _128167 h1)). Qed.
Lemma lem6985313 {A : Type'} (P : A -> Prop) (Q : Prop) : (term113 A P Q) = (term112 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem6985314 {_128167 : Type'} (P : type686 _128167) (Q : Prop) : (term115 _128167 P Q) = (term114 _128167 P Q).
Proof. exact (@lem6985313 (_128167 -> Prop) P Q). Qed.
Lemma lem6985315 {_128167 : Type'} (s : _128167 -> Prop) : (term117 _128167 s) = (term116 _128167 s).
Proof. exact (@lem6985314 _128167 (term118 _128167 s) (@FINITE _128167 s)). Qed.
Lemma lem6985316 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term119 _128167 s t) = (term102 _128167 s t).
Proof. exact (eq_refl (term119 _128167 s t)). Qed.
Lemma lem6985317 {_128167 : Type'} (s : _128167 -> Prop) : (term125 _128167 s) = (term118 _128167 s).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6985316 _128167 s t)). Qed.
Lemma lem6985318 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6985319 {_128167 : Type'} (s : _128167 -> Prop) : (term126 _128167 s) = (term127 _128167 s).
Proof. exact (MK_COMB (@lem6985318 _128167) (@lem6985317 _128167 s)). Qed.
Lemma lem6985320 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6985321 {_128167 : Type'} (s : _128167 -> Prop) : (term128 _128167 s) = (term129 _128167 s).
Proof. exact (MK_COMB (@lem6985320) (@lem6985319 _128167 s)). Qed.
Lemma lem6985322 {_128167 : Type'} (s : _128167 -> Prop) : (@FINITE _128167 s) = (@FINITE _128167 s).
Proof. exact (eq_refl (@FINITE _128167 s)). Qed.
Lemma lem6985323 {_128167 : Type'} (s : _128167 -> Prop) : (term117 _128167 s) = (term130 _128167 s).
Proof. exact (MK_COMB (@lem6985321 _128167 s) (@lem6985322 _128167 s)). Qed.
Lemma lem6985324 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6985325 {_128167 : Type'} (s : _128167 -> Prop) : (term207 _128167 s) = (term208 _128167 s).
Proof. exact (MK_COMB (@lem6985324) (@lem6985323 _128167 s)). Qed.
Lemma lem6985326 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term119 _128167 s t) = (term102 _128167 s t).
Proof. exact (eq_refl (term119 _128167 s t)). Qed.
Lemma lem6985327 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6985328 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term120 _128167 s t) = (term104 _128167 s t).
Proof. exact (MK_COMB (@lem6985327) (@lem6985326 _128167 s t)). Qed.
Lemma lem6985329 {_128167 : Type'} (s : _128167 -> Prop) : (@FINITE _128167 s) = (@FINITE _128167 s).
Proof. exact (eq_refl (@FINITE _128167 s)). Qed.
Lemma lem6985330 {_128167 : Type'} (t : _128167 -> Prop) (s : _128167 -> Prop) : (term121 _128167 t s) = (term106 _128167 t s).
Proof. exact (MK_COMB (@lem6985328 _128167 s t) (@lem6985329 _128167 s)). Qed.
Lemma lem6985331 {_128167 : Type'} (s : _128167 -> Prop) : (term122 _128167 s) = (term108 _128167 s).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6985330 _128167 t s)). Qed.
Lemma lem6985332 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6985333 {_128167 : Type'} (s : _128167 -> Prop) : (term116 _128167 s) = (term109 _128167 s).
Proof. exact (MK_COMB (@lem6985332 _128167) (@lem6985331 _128167 s)). Qed.
Lemma lem6985334 {_128167 : Type'} (s : _128167 -> Prop) : ((term117 _128167 s) = (term116 _128167 s)) = ((term130 _128167 s) = (term109 _128167 s)).
Proof. exact (MK_COMB (@lem6985325 _128167 s) (@lem6985333 _128167 s)). Qed.
Lemma lem6985335 {_128167 : Type'} (s : _128167 -> Prop) : (term130 _128167 s) = (term109 _128167 s).
Proof. exact (EQ_MP (@lem6985334 _128167 s) (@lem6985315 _128167 s)). Qed.
Lemma lem6985336 {_128167 : Type'} : (term131 _128167) = (term110 _128167).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6985335 _128167 s)). Qed.
Lemma lem6985337 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6985338 {_128167 : Type'} : (term132 _128167) = (term111 _128167).
Proof. exact (MK_COMB (@lem6985337 _128167) (@lem6985336 _128167)). Qed.
Lemma lem6985351 {_128167 : Type'} (t : _128167 -> Prop) (s : _128167 -> Prop) : (term106 _128167 t s) = (term106 _128167 t s).
Proof. exact (eq_refl (term106 _128167 t s)). Qed.
Lemma lem6985352 {_128167 : Type'} (s : _128167 -> Prop) : (term108 _128167 s) = (term108 _128167 s).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6985351 _128167 t s)). Qed.
Lemma lem6985353 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6985354 {_128167 : Type'} (s : _128167 -> Prop) : (term109 _128167 s) = (term109 _128167 s).
Proof. exact (MK_COMB (@lem6985353 _128167) (@lem6985352 _128167 s)). Qed.
Lemma lem6985355 {_128167 : Type'} : (term110 _128167) = (term110 _128167).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6985354 _128167 s)). Qed.
Lemma lem6985356 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6985357 {_128167 : Type'} : (term111 _128167) = (term111 _128167).
Proof. exact (MK_COMB (@lem6985356 _128167) (@lem6985355 _128167)). Qed.
Lemma lem6985358 {_128167 : Type'} : (term132 _128167) = (term111 _128167).
Proof. exact (TRANS (@lem6985338 _128167) (@lem6985357 _128167)). Qed.
Lemma lem6985359 {_128167 : Type'} (h1 : term13 _128167) : term111 _128167.
Proof. exact (EQ_MP (@lem6985358 _128167) (@lem6984965 _128167 h1)). Qed.
Lemma lem6985410 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : (term198 _128167 s t f) = (term198 _128167 s t f).
Proof. exact (eq_refl (term198 _128167 s t f)). Qed.
Lemma lem6985411 {_128167 : Type'} (s : _128167 -> Prop) (f : _128167 -> nat) : (term200 _128167 s f) = (term200 _128167 s f).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6985410 _128167 s t f)). Qed.
Lemma lem6985412 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6985413 {_128167 : Type'} (s : _128167 -> Prop) (f : _128167 -> nat) : (term201 _128167 s f) = (term201 _128167 s f).
Proof. exact (MK_COMB (@lem6985412 _128167) (@lem6985411 _128167 s f)). Qed.
Lemma lem6985414 {_128167 : Type'} (f : _128167 -> nat) : (term202 _128167 f) = (term202 _128167 f).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6985413 _128167 s f)). Qed.
Lemma lem6985415 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6985416 {_128167 : Type'} (f : _128167 -> nat) : (term203 _128167 f) = (term203 _128167 f).
Proof. exact (MK_COMB (@lem6985415 _128167) (@lem6985414 _128167 f)). Qed.
Lemma lem6985417 {_128167 : Type'} : (term204 _128167) = (term204 _128167).
Proof. exact (fun_ext (fun f : _128167 -> nat => @lem6985416 _128167 f)). Qed.
Lemma lem6985418 {_128167 : Type'} : (@all (_128167 -> nat)) = (@all (_128167 -> nat)).
Proof. exact (eq_refl (@all (_128167 -> nat))). Qed.
Lemma lem6985420 {_128167 : Type'} : (term205 _128167) = (term205 _128167).
Proof. exact (MK_COMB (@lem6985418 _128167) (@lem6985417 _128167)). Qed.
Lemma lem6985421 {_128167 : Type'} (h1 : term11 _128167) : term205 _128167.
Proof. exact (EQ_MP (@lem6985420 _128167) (@lem6985195 _128167 h1)). Qed.
Lemma lem6985445 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term147 _128167 s t) = (term147 _128167 s t).
Proof. exact (eq_refl (term147 _128167 s t)). Qed.
Lemma lem6985446 {_128167 : Type'} (s : _128167 -> Prop) : (term144 _128167 s) = (term144 _128167 s).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6985445 _128167 s t)). Qed.
Lemma lem6985447 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6985448 {_128167 : Type'} (s : _128167 -> Prop) : (term158 _128167 s) = (term158 _128167 s).
Proof. exact (MK_COMB (@lem6985447 _128167) (@lem6985446 _128167 s)). Qed.
Lemma lem6985449 {_128167 : Type'} : (term169 _128167) = (term169 _128167).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6985448 _128167 s)). Qed.
Lemma lem6985450 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6985452 {_128167 : Type'} : (term180 _128167) = (term180 _128167).
Proof. exact (MK_COMB (@lem6985450 _128167) (@lem6985449 _128167)). Qed.
Lemma lem6985453 {_128167 : Type'} (h1 : term12 _128167) : term180 _128167.
Proof. exact (EQ_MP (@lem6985452 _128167) (@lem6985257 _128167 h1)). Qed.
Lemma lem6985503 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term63 _128167 s t) = (term63 _128167 s t).
Proof. exact (eq_refl (term63 _128167 s t)). Qed.
Lemma lem6985504 {_128167 : Type'} (s : _128167 -> Prop) : (term64 _128167 s) = (term64 _128167 s).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6985503 _128167 s t)). Qed.
Lemma lem6985505 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6985506 {_128167 : Type'} (s : _128167 -> Prop) : (term65 _128167 s) = (term65 _128167 s).
Proof. exact (MK_COMB (@lem6985505 _128167) (@lem6985504 _128167 s)). Qed.
Lemma lem6985507 {_128167 : Type'} : (term66 _128167) = (term66 _128167).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6985506 _128167 s)). Qed.
Lemma lem6985508 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6985510 {_128167 : Type'} : (term67 _128167) = (term67 _128167).
Proof. exact (MK_COMB (@lem6985508 _128167) (@lem6985507 _128167)). Qed.
Lemma lem6985511 {_128167 : Type'} (h1 : term14 _128167) : term67 _128167.
Proof. exact (EQ_MP (@lem6985510 _128167) (@lem6985261 _128167 h1)). Qed.
Lemma lem6985513 {_128167 : Type'} (t : _128167 -> Prop) (s : _128167 -> Prop) : (term58 _128167 t s) = (term58 _128167 t s).
Proof. exact (eq_refl (term58 _128167 t s)). Qed.
Lemma lem6985514 {_128167 : Type'} (s : _128167 -> Prop) : (term59 _128167 s) = (term59 _128167 s).
Proof. exact (fun_ext (fun t : _128167 -> Prop => @lem6985513 _128167 t s)). Qed.
Lemma lem6985515 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6985516 {_128167 : Type'} (s : _128167 -> Prop) : (term60 _128167 s) = (term60 _128167 s).
Proof. exact (MK_COMB (@lem6985515 _128167) (@lem6985514 _128167 s)). Qed.
Lemma lem6985517 {_128167 : Type'} : (term61 _128167) = (term61 _128167).
Proof. exact (fun_ext (fun s : _128167 -> Prop => @lem6985516 _128167 s)). Qed.
Lemma lem6985518 {_128167 : Type'} : (@all (_128167 -> Prop)) = (@all (_128167 -> Prop)).
Proof. exact (eq_refl (@all (_128167 -> Prop))). Qed.
Lemma lem6985520 {_128167 : Type'} : (term62 _128167) = (term62 _128167).
Proof. exact (MK_COMB (@lem6985518 _128167) (@lem6985517 _128167)). Qed.
Lemma lem6985521 {_128167 : Type'} (h1 : term14 _128167) : term62 _128167.
Proof. exact (EQ_MP (@lem6985520 _128167) (@lem6985260 _128167 h1)). Qed.
Lemma lem6985548 {_128167 : Type'} (_92994 : _128167 -> Prop) (h1 : term13 _128167) : term209 _128167 _92994.
Proof. exact (@lem6985359 _128167 h1 _92994). Qed.
Lemma lem6985549 {_128167 : Type'} (_92994 : _128167 -> Prop) : (term209 _128167 _92994) = (term109 _128167 _92994).
Proof. exact (eq_refl (term209 _128167 _92994)). Qed.
Lemma lem6985550 {_128167 : Type'} (_92994 : _128167 -> Prop) (h1 : term13 _128167) : term109 _128167 _92994.
Proof. exact (EQ_MP (@lem6985549 _128167 _92994) (@lem6985548 _128167 _92994 h1)). Qed.
Lemma lem6985551 {_128167 : Type'} (_92994 : _128167 -> Prop) (_92995 : _128167 -> Prop) (h1 : term13 _128167) : term210 _128167 _92994 _92995.
Proof. exact (@lem6985550 _128167 _92994 h1 _92995). Qed.
Lemma lem6985552 {_128167 : Type'} (_92995 : _128167 -> Prop) (_92994 : _128167 -> Prop) : (term210 _128167 _92994 _92995) = (term106 _128167 _92995 _92994).
Proof. exact (eq_refl (term210 _128167 _92994 _92995)). Qed.
Lemma lem6985553 {_128167 : Type'} (_92995 : _128167 -> Prop) (_92994 : _128167 -> Prop) (h1 : term13 _128167) : term106 _128167 _92995 _92994.
Proof. exact (EQ_MP (@lem6985552 _128167 _92995 _92994) (@lem6985551 _128167 _92994 _92995 h1)). Qed.
Lemma lem6985563 {_128167 : Type'} (_92999 : _128167 -> nat) (h1 : term11 _128167) : term211 _128167 _92999.
Proof. exact (@lem6985421 _128167 h1 _92999). Qed.
Lemma lem6985564 {_128167 : Type'} (_92999 : _128167 -> nat) : (term211 _128167 _92999) = (term203 _128167 _92999).
Proof. exact (eq_refl (term211 _128167 _92999)). Qed.
Lemma lem6985565 {_128167 : Type'} (_92999 : _128167 -> nat) (h1 : term11 _128167) : term203 _128167 _92999.
Proof. exact (EQ_MP (@lem6985564 _128167 _92999) (@lem6985563 _128167 _92999 h1)). Qed.
Lemma lem6985566 {_128167 : Type'} (_92999 : _128167 -> nat) (_93000 : _128167 -> Prop) (h1 : term11 _128167) : term212 _128167 _92999 _93000.
Proof. exact (@lem6985565 _128167 _92999 h1 _93000). Qed.
Lemma lem6985567 {_128167 : Type'} (_93000 : _128167 -> Prop) (_92999 : _128167 -> nat) : (term212 _128167 _92999 _93000) = (term201 _128167 _93000 _92999).
Proof. exact (eq_refl (term212 _128167 _92999 _93000)). Qed.
Lemma lem6985568 {_128167 : Type'} (_93000 : _128167 -> Prop) (_92999 : _128167 -> nat) (h1 : term11 _128167) : term201 _128167 _93000 _92999.
Proof. exact (EQ_MP (@lem6985567 _128167 _93000 _92999) (@lem6985566 _128167 _92999 _93000 h1)). Qed.
Lemma lem6985569 {_128167 : Type'} (_93000 : _128167 -> Prop) (_92999 : _128167 -> nat) (_93001 : _128167 -> Prop) (h1 : term11 _128167) : term213 _128167 _93000 _92999 _93001.
Proof. exact (@lem6985568 _128167 _93000 _92999 h1 _93001). Qed.
Lemma lem6985570 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) (_92999 : _128167 -> nat) : (term213 _128167 _93000 _92999 _93001) = (term198 _128167 _93000 _93001 _92999).
Proof. exact (eq_refl (term213 _128167 _93000 _92999 _93001)). Qed.
Lemma lem6985571 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) (_92999 : _128167 -> nat) (h1 : term11 _128167) : term198 _128167 _93000 _93001 _92999.
Proof. exact (EQ_MP (@lem6985570 _128167 _93000 _93001 _92999) (@lem6985569 _128167 _93000 _92999 _93001 h1)). Qed.
Lemma lem6985572 {_128167 : Type'} (_93002 : _128167 -> Prop) (h1 : term12 _128167) : term171 _128167 _93002.
Proof. exact (@lem6985453 _128167 h1 _93002). Qed.
Lemma lem6985573 {_128167 : Type'} (_93002 : _128167 -> Prop) : (term171 _128167 _93002) = (term158 _128167 _93002).
Proof. exact (eq_refl (term171 _128167 _93002)). Qed.
Lemma lem6985574 {_128167 : Type'} (_93002 : _128167 -> Prop) (h1 : term12 _128167) : term158 _128167 _93002.
Proof. exact (EQ_MP (@lem6985573 _128167 _93002) (@lem6985572 _128167 _93002 h1)). Qed.
Lemma lem6985575 {_128167 : Type'} (_93002 : _128167 -> Prop) (_93003 : _128167 -> Prop) (h1 : term12 _128167) : term146 _128167 _93002 _93003.
Proof. exact (@lem6985574 _128167 _93002 h1 _93003). Qed.
Lemma lem6985576 {_128167 : Type'} (_93002 : _128167 -> Prop) (_93003 : _128167 -> Prop) : (term146 _128167 _93002 _93003) = (term147 _128167 _93002 _93003).
Proof. exact (eq_refl (term146 _128167 _93002 _93003)). Qed.
Lemma lem6985596 {_128167 : Type'} (_93010 : _128167 -> Prop) (h1 : term14 _128167) : term214 _128167 _93010.
Proof. exact (@lem6985511 _128167 h1 _93010). Qed.
Lemma lem6985597 {_128167 : Type'} (_93010 : _128167 -> Prop) : (term214 _128167 _93010) = (term65 _128167 _93010).
Proof. exact (eq_refl (term214 _128167 _93010)). Qed.
Lemma lem6985598 {_128167 : Type'} (_93010 : _128167 -> Prop) (h1 : term14 _128167) : term65 _128167 _93010.
Proof. exact (EQ_MP (@lem6985597 _128167 _93010) (@lem6985596 _128167 _93010 h1)). Qed.
Lemma lem6985599 {_128167 : Type'} (_93010 : _128167 -> Prop) (_93011 : _128167 -> Prop) (h1 : term14 _128167) : term215 _128167 _93010 _93011.
Proof. exact (@lem6985598 _128167 _93010 h1 _93011). Qed.
Lemma lem6985600 {_128167 : Type'} (_93010 : _128167 -> Prop) (_93011 : _128167 -> Prop) : (term215 _128167 _93010 _93011) = (term63 _128167 _93010 _93011).
Proof. exact (eq_refl (term215 _128167 _93010 _93011)). Qed.
Lemma lem6985602 {_128167 : Type'} (_93012 : _128167 -> Prop) (h1 : term14 _128167) : term216 _128167 _93012.
Proof. exact (@lem6985521 _128167 h1 _93012). Qed.
Lemma lem6985603 {_128167 : Type'} (_93012 : _128167 -> Prop) : (term216 _128167 _93012) = (term60 _128167 _93012).
Proof. exact (eq_refl (term216 _128167 _93012)). Qed.
Lemma lem6985604 {_128167 : Type'} (_93012 : _128167 -> Prop) (h1 : term14 _128167) : term60 _128167 _93012.
Proof. exact (EQ_MP (@lem6985603 _128167 _93012) (@lem6985602 _128167 _93012 h1)). Qed.
Lemma lem6985605 {_128167 : Type'} (_93012 : _128167 -> Prop) (_93013 : _128167 -> Prop) (h1 : term14 _128167) : term217 _128167 _93012 _93013.
Proof. exact (@lem6985604 _128167 _93012 h1 _93013). Qed.
Lemma lem6985606 {_128167 : Type'} (_93013 : _128167 -> Prop) (_93012 : _128167 -> Prop) : (term217 _128167 _93012 _93013) = (term58 _128167 _93013 _93012).
Proof. exact (eq_refl (term217 _128167 _93012 _93013)). Qed.
Lemma lem6985642 {_128167 : Type'} (_92995 : _128167 -> Prop) (_92994 : _128167 -> Prop) : (term106 _128167 _92995 _92994) = (term218 _128167 _92995 _92994).
Proof. exact (@lem6982967 (term219 _128167 _92995) (term220 _128167 _92994 _92995) (@FINITE _128167 _92994)). Qed.
Lemma lem6985665 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) (_92999 : _128167 -> nat) : (term198 _128167 _93000 _93001 _92999) = (term221 _128167 _93000 _93001 _92999).
Proof. exact (@lem6982967 (term219 _128167 _93000) (term188 _128167 _93000 _93001) ((term194 _128167 _93000 _93001 _92999) = (term78 _128167 _93000 _93001 _92999))). Qed.
Lemma lem6985672 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) (_92999 : _128167 -> nat) : (term222 _128167 _93000 _93001 _92999) = (term223 _128167 _93000 _93001 _92999).
Proof. exact (@lem6982967 (term219 _128167 _93001) (term224 _128167 _93000 _93001) ((term194 _128167 _93000 _93001 _92999) = (term78 _128167 _93000 _93001 _92999))). Qed.
Lemma lem6985673 {_128167 : Type'} (_93000 : _128167 -> Prop) : (term189 _128167 _93000) = (term189 _128167 _93000).
Proof. exact (eq_refl (term189 _128167 _93000)). Qed.
Lemma lem6985676 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) (_92999 : _128167 -> nat) : (term221 _128167 _93000 _93001 _92999) = (term225 _128167 _93000 _93001 _92999).
Proof. exact (MK_COMB (@lem6985673 _128167 _93000) (@lem6985672 _128167 _93000 _93001 _92999)). Qed.
Lemma lem6985678 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) (_92999 : _128167 -> nat) : (term198 _128167 _93000 _93001 _92999) = (term225 _128167 _93000 _93001 _92999).
Proof. exact (TRANS (@lem6985665 _128167 _93000 _93001 _92999) (@lem6985676 _128167 _93000 _93001 _92999)). Qed.
Lemma lem6985681 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term76 _128167 s t u f) : term226 _128167 s t u f.
Proof. exact (proj2 (@lem6985249 _128167 s t u f h1)). Qed.
Lemma lem6985683 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term76 _128167 s t u f) : @FINITE _128167 u.
Proof. exact (proj1 (@lem6985251 _128167 s t u f h1)). Qed.
Lemma lem6985687 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term76 _128167 s t u f) : (@UNION _128167 s t) = u.
Proof. exact (proj2 (@lem6985252 _128167 s t u f h1)). Qed.
Lemma lem6985720 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term76 _128167 s t u f) : u = (@UNION _128167 s t).
Proof. exact (SYM (@lem6985687 _128167 s t u f h1)). Qed.
Lemma lem6985791 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : (term227 _128167 s t f) = (term227 _128167 s t f).
Proof. exact (eq_refl (term227 _128167 s t f)). Qed.
Lemma lem6985792 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term76 _128167 s t u f) : (term228 _128167 s t f u) = (term229 _128167 f s t).
Proof. exact (MK_COMB (@lem6985791 _128167 s t f) (@lem6985720 _128167 s t u f h1)). Qed.
Lemma lem6985793 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : (term229 _128167 f s t) = (term230 _128167 s t f).
Proof. exact (eq_refl (term229 _128167 f s t)). Qed.
Lemma lem6985794 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) (u : _128167 -> Prop) : (term231 _128167 s t f u) = (term231 _128167 s t f u).
Proof. exact (eq_refl (term231 _128167 s t f u)). Qed.
Lemma lem6985795 {_128167 : Type'} (u : _128167 -> Prop) (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : ((term228 _128167 s t f u) = (term229 _128167 f s t)) = ((term228 _128167 s t f u) = (term230 _128167 s t f)).
Proof. exact (MK_COMB (@lem6985794 _128167 s t f u) (@lem6985793 _128167 s t f)). Qed.
Lemma lem6985796 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) : (term228 _128167 s t f u) = (term226 _128167 s t u f).
Proof. exact (eq_refl (term228 _128167 s t f u)). Qed.
Lemma lem6985797 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6985798 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) : (term231 _128167 s t f u) = (term232 _128167 s t u f).
Proof. exact (MK_COMB (@lem6985797) (@lem6985796 _128167 s t u f)). Qed.
Lemma lem6985799 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : (term230 _128167 s t f) = (term230 _128167 s t f).
Proof. exact (eq_refl (term230 _128167 s t f)). Qed.
Lemma lem6985800 {_128167 : Type'} (u : _128167 -> Prop) (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : ((term228 _128167 s t f u) = (term230 _128167 s t f)) = ((term226 _128167 s t u f) = (term230 _128167 s t f)).
Proof. exact (MK_COMB (@lem6985798 _128167 s t u f) (@lem6985799 _128167 s t f)). Qed.
Lemma lem6985801 {_128167 : Type'} (u : _128167 -> Prop) (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : ((term228 _128167 s t f u) = (term229 _128167 f s t)) = ((term226 _128167 s t u f) = (term230 _128167 s t f)).
Proof. exact (TRANS (@lem6985795 _128167 u s t f) (@lem6985800 _128167 u s t f)). Qed.
Lemma lem6985802 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term76 _128167 s t u f) : (term226 _128167 s t u f) = (term230 _128167 s t f).
Proof. exact (EQ_MP (@lem6985801 _128167 u s t f) (@lem6985792 _128167 s t u f h1)). Qed.
Lemma lem6985804 {_128167 : Type'} : (term233 _128167) = (term233 _128167).
Proof. exact (eq_refl (term233 _128167)). Qed.
Lemma lem6985805 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term76 _128167 s t u f) : (term234 _128167 u) = (term235 _128167 s t).
Proof. exact (MK_COMB (@lem6985804 _128167) (@lem6985720 _128167 s t u f h1)). Qed.
Lemma lem6985806 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term235 _128167 s t) = (term236 _128167 s t).
Proof. exact (eq_refl (term235 _128167 s t)). Qed.
Lemma lem6985807 {_128167 : Type'} (u : _128167 -> Prop) : (term237 _128167 u) = (term237 _128167 u).
Proof. exact (eq_refl (term237 _128167 u)). Qed.
Lemma lem6985808 {_128167 : Type'} (u : _128167 -> Prop) (s : _128167 -> Prop) (t : _128167 -> Prop) : ((term234 _128167 u) = (term235 _128167 s t)) = ((term234 _128167 u) = (term236 _128167 s t)).
Proof. exact (MK_COMB (@lem6985807 _128167 u) (@lem6985806 _128167 s t)). Qed.
Lemma lem6985809 {_128167 : Type'} (u : _128167 -> Prop) : (term234 _128167 u) = (@FINITE _128167 u).
Proof. exact (eq_refl (term234 _128167 u)). Qed.
Lemma lem6985810 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6985811 {_128167 : Type'} (u : _128167 -> Prop) : (term237 _128167 u) = (term238 _128167 u).
Proof. exact (MK_COMB (@lem6985810) (@lem6985809 _128167 u)). Qed.
Lemma lem6985812 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term236 _128167 s t) = (term236 _128167 s t).
Proof. exact (eq_refl (term236 _128167 s t)). Qed.
Lemma lem6985813 {_128167 : Type'} (u : _128167 -> Prop) (s : _128167 -> Prop) (t : _128167 -> Prop) : ((term234 _128167 u) = (term236 _128167 s t)) = ((@FINITE _128167 u) = (term236 _128167 s t)).
Proof. exact (MK_COMB (@lem6985811 _128167 u) (@lem6985812 _128167 s t)). Qed.
Lemma lem6985814 {_128167 : Type'} (u : _128167 -> Prop) (s : _128167 -> Prop) (t : _128167 -> Prop) : ((term234 _128167 u) = (term235 _128167 s t)) = ((@FINITE _128167 u) = (term236 _128167 s t)).
Proof. exact (TRANS (@lem6985808 _128167 u s t) (@lem6985813 _128167 u s t)). Qed.
Lemma lem6985815 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term76 _128167 s t u f) : (@FINITE _128167 u) = (term236 _128167 s t).
Proof. exact (EQ_MP (@lem6985814 _128167 u s t) (@lem6985805 _128167 s t u f h1)). Qed.
Lemma lem6985830 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term76 _128167 s t u f) : (@INTER _128167 s t) = (@EMPTY _128167).
Proof. exact (proj1 (@lem6985252 _128167 s t u f h1)). Qed.
Lemma lem6985844 {_128167 : Type'} (_93002 : _128167 -> Prop) (_93003 : _128167 -> Prop) (h1 : term12 _128167) : term147 _128167 _93002 _93003.
Proof. exact (EQ_MP (@lem6985576 _128167 _93002 _93003) (@lem6985575 _128167 _93002 _93003 h1)). Qed.
Lemma lem6985943 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term76 _128167 s t u f) : (@EMPTY _128167) = (@INTER _128167 s t).
Proof. exact (SYM (@lem6985830 _128167 s t u f h1)). Qed.
Lemma lem6985985 {_128167 : Type'} (_92995 : _128167 -> Prop) (_92994 : _128167 -> Prop) (h1 : term13 _128167) : term218 _128167 _92995 _92994.
Proof. exact (EQ_MP (@lem6985642 _128167 _92995 _92994) (@lem6985553 _128167 _92995 _92994 h1)). Qed.
Lemma lem6986013 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) (_92999 : _128167 -> nat) (h1 : term11 _128167) : term225 _128167 _93000 _93001 _92999.
Proof. exact (EQ_MP (@lem6985678 _128167 _93000 _93001 _92999) (@lem6985571 _128167 _93000 _93001 _92999 h1)). Qed.
Lemma lem6986027 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term76 _128167 s t u f) : term230 _128167 s t f.
Proof. exact (EQ_MP (@lem6985802 _128167 s t u f h1) (@lem6985681 _128167 s t u f h1)). Qed.
Lemma lem6986042 {_128167 : Type'} (_93002 : _128167 -> Prop) (_93003 : _128167 -> Prop) : (term239 _128167 _93002 _93003) = (term239 _128167 _93002 _93003).
Proof. exact (eq_refl (term239 _128167 _93002 _93003)). Qed.
Lemma lem6986043 {_128167 : Type'} (_93002 : _128167 -> Prop) (_93003 : _128167 -> Prop) (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term76 _128167 s t u f) : (term240 _128167 _93002 _93003) = (term241 _128167 _93002 _93003 s t).
Proof. exact (MK_COMB (@lem6986042 _128167 _93002 _93003) (@lem6985943 _128167 s t u f h1)). Qed.
Lemma lem6986044 {_128167 : Type'} (_93002 : _128167 -> Prop) (_93003 : _128167 -> Prop) (s : _128167 -> Prop) (t : _128167 -> Prop) : (term241 _128167 _93002 _93003 s t) = (term242 _128167 _93002 _93003 s t).
Proof. exact (eq_refl (term241 _128167 _93002 _93003 s t)). Qed.
Lemma lem6986045 {_128167 : Type'} (_93002 : _128167 -> Prop) (_93003 : _128167 -> Prop) : (term243 _128167 _93002 _93003) = (term243 _128167 _93002 _93003).
Proof. exact (eq_refl (term243 _128167 _93002 _93003)). Qed.
Lemma lem6986046 {_128167 : Type'} (_93002 : _128167 -> Prop) (_93003 : _128167 -> Prop) (s : _128167 -> Prop) (t : _128167 -> Prop) : ((term240 _128167 _93002 _93003) = (term241 _128167 _93002 _93003 s t)) = ((term240 _128167 _93002 _93003) = (term242 _128167 _93002 _93003 s t)).
Proof. exact (MK_COMB (@lem6986045 _128167 _93002 _93003) (@lem6986044 _128167 _93002 _93003 s t)). Qed.
Lemma lem6986047 {_128167 : Type'} (_93002 : _128167 -> Prop) (_93003 : _128167 -> Prop) : (term240 _128167 _93002 _93003) = (term147 _128167 _93002 _93003).
Proof. exact (eq_refl (term240 _128167 _93002 _93003)). Qed.
Lemma lem6986048 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6986049 {_128167 : Type'} (_93002 : _128167 -> Prop) (_93003 : _128167 -> Prop) : (term243 _128167 _93002 _93003) = (term244 _128167 _93002 _93003).
Proof. exact (MK_COMB (@lem6986048) (@lem6986047 _128167 _93002 _93003)). Qed.
Lemma lem6986050 {_128167 : Type'} (_93002 : _128167 -> Prop) (_93003 : _128167 -> Prop) (s : _128167 -> Prop) (t : _128167 -> Prop) : (term242 _128167 _93002 _93003 s t) = (term242 _128167 _93002 _93003 s t).
Proof. exact (eq_refl (term242 _128167 _93002 _93003 s t)). Qed.
Lemma lem6986051 {_128167 : Type'} (_93002 : _128167 -> Prop) (_93003 : _128167 -> Prop) (s : _128167 -> Prop) (t : _128167 -> Prop) : ((term240 _128167 _93002 _93003) = (term242 _128167 _93002 _93003 s t)) = ((term147 _128167 _93002 _93003) = (term242 _128167 _93002 _93003 s t)).
Proof. exact (MK_COMB (@lem6986049 _128167 _93002 _93003) (@lem6986050 _128167 _93002 _93003 s t)). Qed.
Lemma lem6986052 {_128167 : Type'} (_93002 : _128167 -> Prop) (_93003 : _128167 -> Prop) (s : _128167 -> Prop) (t : _128167 -> Prop) : ((term240 _128167 _93002 _93003) = (term241 _128167 _93002 _93003 s t)) = ((term147 _128167 _93002 _93003) = (term242 _128167 _93002 _93003 s t)).
Proof. exact (TRANS (@lem6986046 _128167 _93002 _93003 s t) (@lem6986051 _128167 _93002 _93003 s t)). Qed.
Lemma lem6986053 {_128167 : Type'} (_93002 : _128167 -> Prop) (_93003 : _128167 -> Prop) (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term76 _128167 s t u f) : (term147 _128167 _93002 _93003) = (term242 _128167 _93002 _93003 s t).
Proof. exact (EQ_MP (@lem6986052 _128167 _93002 _93003 s t) (@lem6986043 _128167 _93002 _93003 s t u f h1)). Qed.
Lemma lem6986054 {_128167 : Type'} (_93002 : _128167 -> Prop) (_93003 : _128167 -> Prop) (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term76 _128167 s t u f) : term242 _128167 _93002 _93003 s t.
Proof. exact (EQ_MP (@lem6986053 _128167 _93002 _93003 s t u f h2) (@lem6985844 _128167 _93002 _93003 h1)). Qed.
Lemma lem6986358 (x : nat) (y : nat) (z : nat) : term245 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem6986368 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term76 _128167 s t u f) : term236 _128167 s t.
Proof. exact (EQ_MP (@lem6985815 _128167 s t u f h1) (@lem6985683 _128167 s t u f h1)). Qed.
Lemma lem6986369 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term76 _128167 s t u f) : term246 _128167 s t.
Proof. exact (fun h0 : term247 _128167 s t => @lem6986368 _128167 s t u f h1). Qed.
Lemma lem6986371 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6986372 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term246 _128167 s t) = (term236 _128167 s t).
Proof. exact (@lem6986371 (term236 _128167 s t)). Qed.
Lemma lem6986373 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term76 _128167 s t u f) : term236 _128167 s t.
Proof. exact (EQ_MP (@lem6986372 _128167 s t) (@lem6986369 _128167 s t u f h1)). Qed.
Lemma lem6986375 {_128167 : Type'} (_93010 : _128167 -> Prop) (_93011 : _128167 -> Prop) (h1 : term14 _128167) : term63 _128167 _93010 _93011.
Proof. exact (EQ_MP (@lem6985600 _128167 _93010 _93011) (@lem6985599 _128167 _93010 _93011 h1)). Qed.
Lemma lem6986376 {_128167 : Type'} (_93010 : _128167 -> Prop) (_93011 : _128167 -> Prop) (h1 : term14 _128167) : term63 _128167 _93010 _93011.
Proof. exact (@lem6986375 _128167 _93010 _93011 h1). Qed.
Lemma lem6986377 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (h1 : term14 _128167) : term63 _128167 s t.
Proof. exact (@lem6986376 _128167 s t h1). Qed.
Lemma lem6986378 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (h1 : term14 _128167) : term249 _128167 s t.
Proof. exact (fun h0 : term250 _128167 s t => @lem6986377 _128167 s t h1). Qed.
Lemma lem6986380 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6986381 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term249 _128167 s t) = (term63 _128167 s t).
Proof. exact (@lem6986380 (term63 _128167 s t)). Qed.
Lemma lem6986382 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (h1 : term14 _128167) : term63 _128167 s t.
Proof. exact (EQ_MP (@lem6986381 _128167 s t) (@lem6986378 _128167 s t h1)). Qed.
Lemma lem6986398 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6986399 {_128167 : Type'} (_92994 : _128167 -> Prop) (_92995 : _128167 -> Prop) : (term251 _128167 _92995 _92994) = (term252 _128167 _92994 _92995).
Proof. exact (@lem6986398 (@FINITE _128167 _92994) (term220 _128167 _92994 _92995)). Qed.
Lemma lem6986405 {_128167 : Type'} (_92995 : _128167 -> Prop) : (term189 _128167 _92995) = (term189 _128167 _92995).
Proof. exact (eq_refl (term189 _128167 _92995)). Qed.
Lemma lem6986406 {_128167 : Type'} (_92994 : _128167 -> Prop) (_92995 : _128167 -> Prop) : (term218 _128167 _92995 _92994) = (term253 _128167 _92994 _92995).
Proof. exact (MK_COMB (@lem6986405 _128167 _92995) (@lem6986399 _128167 _92994 _92995)). Qed.
Lemma lem6986410 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6986411 {_128167 : Type'} (_92994 : _128167 -> Prop) (_92995 : _128167 -> Prop) : (term253 _128167 _92994 _92995) = (term254 _128167 _92994 _92995).
Proof. exact (@lem6986410 (@FINITE _128167 _92994) (term219 _128167 _92995) (term220 _128167 _92994 _92995)). Qed.
Lemma lem6986427 {_128167 : Type'} (_92994 : _128167 -> Prop) (_92995 : _128167 -> Prop) : (term218 _128167 _92995 _92994) = (term254 _128167 _92994 _92995).
Proof. exact (TRANS (@lem6986406 _128167 _92994 _92995) (@lem6986411 _128167 _92994 _92995)). Qed.
Lemma lem6986428 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6986429 {_128167 : Type'} (_92994 : _128167 -> Prop) (_92995 : _128167 -> Prop) : (term255 _128167 _92995 _92994) = (term256 _128167 _92994 _92995).
Proof. exact (MK_COMB (@lem6986428) (@lem6986427 _128167 _92994 _92995)). Qed.
Lemma lem6986445 {_128167 : Type'} (_92994 : _128167 -> Prop) (_92995 : _128167 -> Prop) : (term254 _128167 _92994 _92995) = (term254 _128167 _92994 _92995).
Proof. exact (eq_refl (term254 _128167 _92994 _92995)). Qed.
Lemma lem6986446 {_128167 : Type'} (_92994 : _128167 -> Prop) (_92995 : _128167 -> Prop) : ((term218 _128167 _92995 _92994) = (term254 _128167 _92994 _92995)) = ((term254 _128167 _92994 _92995) = (term254 _128167 _92994 _92995)).
Proof. exact (MK_COMB (@lem6986429 _128167 _92994 _92995) (@lem6986445 _128167 _92994 _92995)). Qed.
Lemma lem6986448 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6986449 (x : Prop) : (x = x) = True.
Proof. exact (@lem6986448 Prop x). Qed.
Lemma lem6986450 {_128167 : Type'} (_92994 : _128167 -> Prop) (_92995 : _128167 -> Prop) : ((term254 _128167 _92994 _92995) = (term254 _128167 _92994 _92995)) = True.
Proof. exact (@lem6986449 (term254 _128167 _92994 _92995)). Qed.
Lemma lem6986451 {_128167 : Type'} (_92994 : _128167 -> Prop) (_92995 : _128167 -> Prop) : ((term218 _128167 _92995 _92994) = (term254 _128167 _92994 _92995)) = True.
Proof. exact (TRANS (@lem6986446 _128167 _92994 _92995) (@lem6986450 _128167 _92994 _92995)). Qed.
Lemma lem6986452 {_128167 : Type'} (_92994 : _128167 -> Prop) (_92995 : _128167 -> Prop) : True = ((term218 _128167 _92995 _92994) = (term254 _128167 _92994 _92995)).
Proof. exact (SYM (@lem6986451 _128167 _92994 _92995)). Qed.
Lemma lem6986453 {_128167 : Type'} (_92994 : _128167 -> Prop) (_92995 : _128167 -> Prop) : (term218 _128167 _92995 _92994) = (term254 _128167 _92994 _92995).
Proof. exact (EQ_MP (@lem6986452 _128167 _92994 _92995) (@lem0)). Qed.
Lemma lem6986454 {_128167 : Type'} (_92994 : _128167 -> Prop) (_92995 : _128167 -> Prop) (h1 : term13 _128167) : term254 _128167 _92994 _92995.
Proof. exact (EQ_MP (@lem6986453 _128167 _92994 _92995) (@lem6985985 _128167 _92995 _92994 h1)). Qed.
Lemma lem6986456 (b : Prop) (a : Prop) : (a \/ b) = (term257 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6986457 {_128167 : Type'} (_92995 : _128167 -> Prop) (_92994 : _128167 -> Prop) : (term254 _128167 _92994 _92995) = (term258 _128167 _92995 _92994).
Proof. exact (@lem6986456 (term102 _128167 _92994 _92995) (@FINITE _128167 _92994)). Qed.
Lemma lem6986459 (a : Prop) (b : Prop) : (term259 a b) = (term260 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6986460 {_128167 : Type'} (_92994 : _128167 -> Prop) (_92995 : _128167 -> Prop) : (term261 _128167 _92994 _92995) = (term262 _128167 _92994 _92995).
Proof. exact (@lem6986459 (term219 _128167 _92995) (term220 _128167 _92994 _92995)). Qed.
Lemma lem6986462 (a : Prop) : (term263 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6986463 {_128167 : Type'} (_92995 : _128167 -> Prop) : (term264 _128167 _92995) = (@FINITE _128167 _92995).
Proof. exact (@lem6986462 (@FINITE _128167 _92995)). Qed.
Lemma lem6986464 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6986465 {_128167 : Type'} (_92995 : _128167 -> Prop) : (term265 _128167 _92995) = (term266 _128167 _92995).
Proof. exact (MK_COMB (@lem6986464) (@lem6986463 _128167 _92995)). Qed.
Lemma lem6986467 (a : Prop) : (term263 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6986468 {_128167 : Type'} (_92994 : _128167 -> Prop) (_92995 : _128167 -> Prop) : (term267 _128167 _92994 _92995) = (@SUBSET _128167 _92994 _92995).
Proof. exact (@lem6986467 (@SUBSET _128167 _92994 _92995)). Qed.
Lemma lem6986469 {_128167 : Type'} (_92994 : _128167 -> Prop) (_92995 : _128167 -> Prop) : (term262 _128167 _92994 _92995) = (term107 _128167 _92994 _92995).
Proof. exact (MK_COMB (@lem6986465 _128167 _92995) (@lem6986468 _128167 _92994 _92995)). Qed.
Lemma lem6986470 {_128167 : Type'} (_92994 : _128167 -> Prop) (_92995 : _128167 -> Prop) : (term261 _128167 _92994 _92995) = (term107 _128167 _92994 _92995).
Proof. exact (TRANS (@lem6986460 _128167 _92994 _92995) (@lem6986469 _128167 _92994 _92995)). Qed.
Lemma lem6986471 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6986472 {_128167 : Type'} (_92994 : _128167 -> Prop) (_92995 : _128167 -> Prop) : (term268 _128167 _92994 _92995) = (term269 _128167 _92994 _92995).
Proof. exact (MK_COMB (@lem6986471) (@lem6986470 _128167 _92994 _92995)). Qed.
Lemma lem6986473 {_128167 : Type'} (_92994 : _128167 -> Prop) : (@FINITE _128167 _92994) = (@FINITE _128167 _92994).
Proof. exact (eq_refl (@FINITE _128167 _92994)). Qed.
Lemma lem6986474 {_128167 : Type'} (_92995 : _128167 -> Prop) (_92994 : _128167 -> Prop) : (term258 _128167 _92995 _92994) = (term54 _128167 _92995 _92994).
Proof. exact (MK_COMB (@lem6986472 _128167 _92994 _92995) (@lem6986473 _128167 _92994)). Qed.
Lemma lem6986475 {_128167 : Type'} (_92995 : _128167 -> Prop) (_92994 : _128167 -> Prop) : (term254 _128167 _92994 _92995) = (term54 _128167 _92995 _92994).
Proof. exact (TRANS (@lem6986457 _128167 _92995 _92994) (@lem6986474 _128167 _92995 _92994)). Qed.
Lemma lem6986477 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term14 _128167) (h2 : term76 _128167 s t u f) : term270 _128167 s t.
Proof. exact (conj (@lem6986373 _128167 s t u f h2) (@lem6986382 _128167 s t h1)). Qed.
Lemma lem6986479 {_128167 : Type'} (_92995 : _128167 -> Prop) (_92994 : _128167 -> Prop) (h1 : term13 _128167) : term54 _128167 _92995 _92994.
Proof. exact (EQ_MP (@lem6986475 _128167 _92995 _92994) (@lem6986454 _128167 _92994 _92995 h1)). Qed.
Lemma lem6986480 {_128167 : Type'} (_92995 : _128167 -> Prop) (_92994 : _128167 -> Prop) (h1 : term13 _128167) : term54 _128167 _92995 _92994.
Proof. exact (@lem6986479 _128167 _92995 _92994 h1). Qed.
Lemma lem6986481 {_128167 : Type'} (t : _128167 -> Prop) (s : _128167 -> Prop) (h1 : term13 _128167) : term271 _128167 t s.
Proof. exact (@lem6986480 _128167 (@UNION _128167 s t) s h1). Qed.
Lemma lem6986484 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term13 _128167) (h2 : term14 _128167) (h3 : term76 _128167 s t u f) : @FINITE _128167 s.
Proof. exact (@lem6986481 _128167 t s h1 (@lem6986477 _128167 s t u f h2 h3)). Qed.
Lemma lem6986485 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term13 _128167) (h2 : term14 _128167) (h3 : term76 _128167 s t u f) : term272 _128167 s.
Proof. exact (fun h0 : term219 _128167 s => @lem6986484 _128167 s t u f h1 h2 h3). Qed.
Lemma lem6986487 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6986488 {_128167 : Type'} (s : _128167 -> Prop) : (term272 _128167 s) = (@FINITE _128167 s).
Proof. exact (@lem6986487 (@FINITE _128167 s)). Qed.
Lemma lem6986489 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term13 _128167) (h2 : term14 _128167) (h3 : term76 _128167 s t u f) : @FINITE _128167 s.
Proof. exact (EQ_MP (@lem6986488 _128167 s) (@lem6986485 _128167 s t u f h1 h2 h3)). Qed.
Lemma lem6986491 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term76 _128167 s t u f) : term236 _128167 s t.
Proof. exact (EQ_MP (@lem6985815 _128167 s t u f h1) (@lem6985683 _128167 s t u f h1)). Qed.
Lemma lem6986492 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term76 _128167 s t u f) : term246 _128167 s t.
Proof. exact (fun h0 : term247 _128167 s t => @lem6986491 _128167 s t u f h1). Qed.
Lemma lem6986494 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6986495 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term246 _128167 s t) = (term236 _128167 s t).
Proof. exact (@lem6986494 (term236 _128167 s t)). Qed.
Lemma lem6986496 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term76 _128167 s t u f) : term236 _128167 s t.
Proof. exact (EQ_MP (@lem6986495 _128167 s t) (@lem6986492 _128167 s t u f h1)). Qed.
Lemma lem6986498 {_128167 : Type'} (_93013 : _128167 -> Prop) (_93012 : _128167 -> Prop) (h1 : term14 _128167) : term58 _128167 _93013 _93012.
Proof. exact (EQ_MP (@lem6985606 _128167 _93013 _93012) (@lem6985605 _128167 _93012 _93013 h1)). Qed.
Lemma lem6986499 {_128167 : Type'} (_93013 : _128167 -> Prop) (_93012 : _128167 -> Prop) (h1 : term14 _128167) : term58 _128167 _93013 _93012.
Proof. exact (@lem6986498 _128167 _93013 _93012 h1). Qed.
Lemma lem6986500 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (h1 : term14 _128167) : term58 _128167 s t.
Proof. exact (@lem6986499 _128167 s t h1). Qed.
Lemma lem6986501 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (h1 : term14 _128167) : term273 _128167 s t.
Proof. exact (fun h0 : term274 _128167 s t => @lem6986500 _128167 s t h1). Qed.
Lemma lem6986503 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6986504 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term273 _128167 s t) = (term58 _128167 s t).
Proof. exact (@lem6986503 (term58 _128167 s t)). Qed.
Lemma lem6986505 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (h1 : term14 _128167) : term58 _128167 s t.
Proof. exact (EQ_MP (@lem6986504 _128167 s t) (@lem6986501 _128167 s t h1)). Qed.
Lemma lem6986506 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term14 _128167) (h2 : term76 _128167 s t u f) : term275 _128167 s t.
Proof. exact (conj (@lem6986496 _128167 s t u f h2) (@lem6986505 _128167 s t h1)). Qed.
Lemma lem6986508 {_128167 : Type'} (_92995 : _128167 -> Prop) (_92994 : _128167 -> Prop) (h1 : term13 _128167) : term54 _128167 _92995 _92994.
Proof. exact (EQ_MP (@lem6986475 _128167 _92995 _92994) (@lem6986454 _128167 _92994 _92995 h1)). Qed.
Lemma lem6986509 {_128167 : Type'} (_92995 : _128167 -> Prop) (_92994 : _128167 -> Prop) (h1 : term13 _128167) : term54 _128167 _92995 _92994.
Proof. exact (@lem6986508 _128167 _92995 _92994 h1). Qed.
Lemma lem6986510 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (h1 : term13 _128167) : term276 _128167 s t.
Proof. exact (@lem6986509 _128167 (@UNION _128167 s t) t h1). Qed.
Lemma lem6986513 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term13 _128167) (h2 : term14 _128167) (h3 : term76 _128167 s t u f) : @FINITE _128167 t.
Proof. exact (@lem6986510 _128167 s t h1 (@lem6986506 _128167 s t u f h2 h3)). Qed.
Lemma lem6986514 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term13 _128167) (h2 : term14 _128167) (h3 : term76 _128167 s t u f) : term272 _128167 t.
Proof. exact (fun h0 : term219 _128167 t => @lem6986513 _128167 s t u f h1 h2 h3). Qed.
Lemma lem6986516 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6986517 {_128167 : Type'} (t : _128167 -> Prop) : (term272 _128167 t) = (@FINITE _128167 t).
Proof. exact (@lem6986516 (@FINITE _128167 t)). Qed.
Lemma lem6986518 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term13 _128167) (h2 : term14 _128167) (h3 : term76 _128167 s t u f) : @FINITE _128167 t.
Proof. exact (EQ_MP (@lem6986517 _128167 t) (@lem6986514 _128167 s t u f h1 h2 h3)). Qed.
Lemma lem6986520 {_128167 : Type'} (x : _128167 -> Prop) : x = x.
Proof. exact (@lem21386 (_128167 -> Prop) x). Qed.
Lemma lem6986521 {_128167 : Type'} (x : _128167 -> Prop) : x = x.
Proof. exact (@lem6986520 _128167 x). Qed.
Lemma lem6986522 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (@INTER _128167 s t) = (@INTER _128167 s t).
Proof. exact (@lem6986521 _128167 (@INTER _128167 s t)). Qed.
Lemma lem6986523 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : term277 _128167 s t.
Proof. exact (fun h0 : term278 _128167 s t => @lem6986522 _128167 s t). Qed.
Lemma lem6986525 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6986526 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term277 _128167 s t) = ((@INTER _128167 s t) = (@INTER _128167 s t)).
Proof. exact (@lem6986525 ((@INTER _128167 s t) = (@INTER _128167 s t))). Qed.
Lemma lem6986527 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (@INTER _128167 s t) = (@INTER _128167 s t).
Proof. exact (EQ_MP (@lem6986526 _128167 s t) (@lem6986523 _128167 s t)). Qed.
Lemma lem6986529 (b : Prop) (a : Prop) : (a \/ b) = (term257 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6986530 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (_93002 : _128167 -> Prop) (_93003 : _128167 -> Prop) : (term242 _128167 _93002 _93003 s t) = (term279 _128167 s t _93002 _93003).
Proof. exact (@lem6986529 (term280 _128167 _93002 _93003 s t) (@DISJOINT _128167 _93002 _93003)). Qed.
Lemma lem6986532 (a : Prop) : (term263 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6986533 {_128167 : Type'} (_93002 : _128167 -> Prop) (_93003 : _128167 -> Prop) (s : _128167 -> Prop) (t : _128167 -> Prop) : (term281 _128167 _93002 _93003 s t) = ((@INTER _128167 _93002 _93003) = (@INTER _128167 s t)).
Proof. exact (@lem6986532 ((@INTER _128167 _93002 _93003) = (@INTER _128167 s t))). Qed.
Lemma lem6986534 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6986535 {_128167 : Type'} (_93002 : _128167 -> Prop) (_93003 : _128167 -> Prop) (s : _128167 -> Prop) (t : _128167 -> Prop) : (term282 _128167 _93002 _93003 s t) = (term283 _128167 _93002 _93003 s t).
Proof. exact (MK_COMB (@lem6986534) (@lem6986533 _128167 _93002 _93003 s t)). Qed.
Lemma lem6986536 {_128167 : Type'} (_93002 : _128167 -> Prop) (_93003 : _128167 -> Prop) : (@DISJOINT _128167 _93002 _93003) = (@DISJOINT _128167 _93002 _93003).
Proof. exact (eq_refl (@DISJOINT _128167 _93002 _93003)). Qed.
Lemma lem6986537 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (_93002 : _128167 -> Prop) (_93003 : _128167 -> Prop) : (term279 _128167 s t _93002 _93003) = (term284 _128167 s t _93002 _93003).
Proof. exact (MK_COMB (@lem6986535 _128167 _93002 _93003 s t) (@lem6986536 _128167 _93002 _93003)). Qed.
Lemma lem6986538 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (_93002 : _128167 -> Prop) (_93003 : _128167 -> Prop) : (term242 _128167 _93002 _93003 s t) = (term284 _128167 s t _93002 _93003).
Proof. exact (TRANS (@lem6986530 _128167 s t _93002 _93003) (@lem6986537 _128167 s t _93002 _93003)). Qed.
Lemma lem6986541 {_128167 : Type'} (_93002 : _128167 -> Prop) (_93003 : _128167 -> Prop) (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term76 _128167 s t u f) : term284 _128167 s t _93002 _93003.
Proof. exact (EQ_MP (@lem6986538 _128167 s t _93002 _93003) (@lem6986054 _128167 _93002 _93003 s t u f h1 h2)). Qed.
Lemma lem6986542 {_128167 : Type'} (_93002 : _128167 -> Prop) (_93003 : _128167 -> Prop) (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term76 _128167 s t u f) : term284 _128167 s t _93002 _93003.
Proof. exact (@lem6986541 _128167 _93002 _93003 s t u f h1 h2). Qed.
Lemma lem6986543 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term76 _128167 s t u f) : term285 _128167 s t.
Proof. exact (@lem6986542 _128167 s t s t u f h1 h2). Qed.
Lemma lem6986546 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term76 _128167 s t u f) : @DISJOINT _128167 s t.
Proof. exact (@lem6986543 _128167 s t u f h1 h2 (@lem6986527 _128167 s t)). Qed.
Lemma lem6986547 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term76 _128167 s t u f) : term286 _128167 s t.
Proof. exact (fun h0 : term224 _128167 s t => @lem6986546 _128167 s t u f h1 h2). Qed.
Lemma lem6986549 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6986550 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) : (term286 _128167 s t) = (@DISJOINT _128167 s t).
Proof. exact (@lem6986549 (@DISJOINT _128167 s t)). Qed.
Lemma lem6986551 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term76 _128167 s t u f) : @DISJOINT _128167 s t.
Proof. exact (EQ_MP (@lem6986550 _128167 s t) (@lem6986547 _128167 s t u f h1 h2)). Qed.
Lemma lem6986567 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6986568 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) (_92999 : _128167 -> nat) : (term223 _128167 _93000 _93001 _92999) = (term287 _128167 _93000 _93001 _92999).
Proof. exact (@lem6986567 (term224 _128167 _93000 _93001) (term219 _128167 _93001) ((term194 _128167 _93000 _93001 _92999) = (term78 _128167 _93000 _93001 _92999))). Qed.
Lemma lem6986582 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6986583 {_128167 : Type'} (_93000 : _128167 -> Prop) (_92999 : _128167 -> nat) (_93001 : _128167 -> Prop) : (term288 _128167 _93000 _93001 _92999) = (term289 _128167 _93000 _92999 _93001).
Proof. exact (@lem6986582 ((term194 _128167 _93000 _93001 _92999) = (term78 _128167 _93000 _93001 _92999)) (term219 _128167 _93001)). Qed.
Lemma lem6986591 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : (term290 _128167 _93000 _93001) = (term290 _128167 _93000 _93001).
Proof. exact (eq_refl (term290 _128167 _93000 _93001)). Qed.
Lemma lem6986592 {_128167 : Type'} (_93000 : _128167 -> Prop) (_92999 : _128167 -> nat) (_93001 : _128167 -> Prop) : (term287 _128167 _93000 _93001 _92999) = (term291 _128167 _93000 _92999 _93001).
Proof. exact (MK_COMB (@lem6986591 _128167 _93000 _93001) (@lem6986583 _128167 _93000 _92999 _93001)). Qed.
Lemma lem6986596 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6986597 {_128167 : Type'} (_92999 : _128167 -> nat) (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : (term291 _128167 _93000 _92999 _93001) = (term292 _128167 _92999 _93000 _93001).
Proof. exact (@lem6986596 ((term194 _128167 _93000 _93001 _92999) = (term78 _128167 _93000 _93001 _92999)) (term224 _128167 _93000 _93001) (term219 _128167 _93001)). Qed.
Lemma lem6986615 {_128167 : Type'} (_92999 : _128167 -> nat) (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : (term287 _128167 _93000 _93001 _92999) = (term292 _128167 _92999 _93000 _93001).
Proof. exact (TRANS (@lem6986592 _128167 _93000 _92999 _93001) (@lem6986597 _128167 _92999 _93000 _93001)). Qed.
Lemma lem6986616 {_128167 : Type'} (_92999 : _128167 -> nat) (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : (term223 _128167 _93000 _93001 _92999) = (term292 _128167 _92999 _93000 _93001).
Proof. exact (TRANS (@lem6986568 _128167 _93000 _93001 _92999) (@lem6986615 _128167 _92999 _93000 _93001)). Qed.
Lemma lem6986617 {_128167 : Type'} (_93000 : _128167 -> Prop) : (term189 _128167 _93000) = (term189 _128167 _93000).
Proof. exact (eq_refl (term189 _128167 _93000)). Qed.
Lemma lem6986618 {_128167 : Type'} (_92999 : _128167 -> nat) (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : (term225 _128167 _93000 _93001 _92999) = (term293 _128167 _92999 _93000 _93001).
Proof. exact (MK_COMB (@lem6986617 _128167 _93000) (@lem6986616 _128167 _92999 _93000 _93001)). Qed.
Lemma lem6986622 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6986623 {_128167 : Type'} (_92999 : _128167 -> nat) (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : (term293 _128167 _92999 _93000 _93001) = (term294 _128167 _92999 _93000 _93001).
Proof. exact (@lem6986622 ((term194 _128167 _93000 _93001 _92999) = (term78 _128167 _93000 _93001 _92999)) (term219 _128167 _93000) (term295 _128167 _93000 _93001)). Qed.
Lemma lem6986639 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6986640 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : (term296 _128167 _93000 _93001) = (term297 _128167 _93000 _93001).
Proof. exact (@lem6986639 (term224 _128167 _93000 _93001) (term219 _128167 _93000) (term219 _128167 _93001)). Qed.
Lemma lem6986656 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) (_92999 : _128167 -> nat) : (term298 _128167 _93000 _93001 _92999) = (term298 _128167 _93000 _93001 _92999).
Proof. exact (eq_refl (term298 _128167 _93000 _93001 _92999)). Qed.
Lemma lem6986657 {_128167 : Type'} (_92999 : _128167 -> nat) (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : (term294 _128167 _92999 _93000 _93001) = (term299 _128167 _92999 _93000 _93001).
Proof. exact (MK_COMB (@lem6986656 _128167 _93000 _93001 _92999) (@lem6986640 _128167 _93000 _93001)). Qed.
Lemma lem6986668 {_128167 : Type'} (_92999 : _128167 -> nat) (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : (term293 _128167 _92999 _93000 _93001) = (term299 _128167 _92999 _93000 _93001).
Proof. exact (TRANS (@lem6986623 _128167 _92999 _93000 _93001) (@lem6986657 _128167 _92999 _93000 _93001)). Qed.
Lemma lem6986669 {_128167 : Type'} (_92999 : _128167 -> nat) (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : (term225 _128167 _93000 _93001 _92999) = (term299 _128167 _92999 _93000 _93001).
Proof. exact (TRANS (@lem6986618 _128167 _92999 _93000 _93001) (@lem6986668 _128167 _92999 _93000 _93001)). Qed.
Lemma lem6986670 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6986671 {_128167 : Type'} (_92999 : _128167 -> nat) (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : (term300 _128167 _93000 _93001 _92999) = (term301 _128167 _92999 _93000 _93001).
Proof. exact (MK_COMB (@lem6986670) (@lem6986669 _128167 _92999 _93000 _93001)). Qed.
Lemma lem6986697 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6986698 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : (term188 _128167 _93000 _93001) = (term295 _128167 _93000 _93001).
Proof. exact (@lem6986697 (term224 _128167 _93000 _93001) (term219 _128167 _93001)). Qed.
Lemma lem6986704 {_128167 : Type'} (_93000 : _128167 -> Prop) : (term189 _128167 _93000) = (term189 _128167 _93000).
Proof. exact (eq_refl (term189 _128167 _93000)). Qed.
Lemma lem6986705 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : (term191 _128167 _93000 _93001) = (term296 _128167 _93000 _93001).
Proof. exact (MK_COMB (@lem6986704 _128167 _93000) (@lem6986698 _128167 _93000 _93001)). Qed.
Lemma lem6986709 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6986710 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : (term296 _128167 _93000 _93001) = (term297 _128167 _93000 _93001).
Proof. exact (@lem6986709 (term224 _128167 _93000 _93001) (term219 _128167 _93000) (term219 _128167 _93001)). Qed.
Lemma lem6986726 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : (term191 _128167 _93000 _93001) = (term297 _128167 _93000 _93001).
Proof. exact (TRANS (@lem6986705 _128167 _93000 _93001) (@lem6986710 _128167 _93000 _93001)). Qed.
Lemma lem6986727 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) (_92999 : _128167 -> nat) : (term298 _128167 _93000 _93001 _92999) = (term298 _128167 _93000 _93001 _92999).
Proof. exact (eq_refl (term298 _128167 _93000 _93001 _92999)). Qed.
Lemma lem6986728 {_128167 : Type'} (_92999 : _128167 -> nat) (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : (term302 _128167 _92999 _93000 _93001) = (term299 _128167 _92999 _93000 _93001).
Proof. exact (MK_COMB (@lem6986727 _128167 _93000 _93001 _92999) (@lem6986726 _128167 _93000 _93001)). Qed.
Lemma lem6986739 {_128167 : Type'} (_92999 : _128167 -> nat) (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : ((term225 _128167 _93000 _93001 _92999) = (term302 _128167 _92999 _93000 _93001)) = ((term299 _128167 _92999 _93000 _93001) = (term299 _128167 _92999 _93000 _93001)).
Proof. exact (MK_COMB (@lem6986671 _128167 _92999 _93000 _93001) (@lem6986728 _128167 _92999 _93000 _93001)). Qed.
Lemma lem6986741 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6986742 (x : Prop) : (x = x) = True.
Proof. exact (@lem6986741 Prop x). Qed.
Lemma lem6986743 {_128167 : Type'} (_92999 : _128167 -> nat) (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : ((term299 _128167 _92999 _93000 _93001) = (term299 _128167 _92999 _93000 _93001)) = True.
Proof. exact (@lem6986742 (term299 _128167 _92999 _93000 _93001)). Qed.
Lemma lem6986744 {_128167 : Type'} (_92999 : _128167 -> nat) (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : ((term225 _128167 _93000 _93001 _92999) = (term302 _128167 _92999 _93000 _93001)) = True.
Proof. exact (TRANS (@lem6986739 _128167 _92999 _93000 _93001) (@lem6986743 _128167 _92999 _93000 _93001)). Qed.
Lemma lem6986745 {_128167 : Type'} (_92999 : _128167 -> nat) (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : True = ((term225 _128167 _93000 _93001 _92999) = (term302 _128167 _92999 _93000 _93001)).
Proof. exact (SYM (@lem6986744 _128167 _92999 _93000 _93001)). Qed.
Lemma lem6986746 {_128167 : Type'} (_92999 : _128167 -> nat) (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : (term225 _128167 _93000 _93001 _92999) = (term302 _128167 _92999 _93000 _93001).
Proof. exact (EQ_MP (@lem6986745 _128167 _92999 _93000 _93001) (@lem0)). Qed.
Lemma lem6986747 {_128167 : Type'} (_92999 : _128167 -> nat) (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) (h1 : term11 _128167) : term302 _128167 _92999 _93000 _93001.
Proof. exact (EQ_MP (@lem6986746 _128167 _92999 _93000 _93001) (@lem6986013 _128167 _93000 _93001 _92999 h1)). Qed.
Lemma lem6986749 (b : Prop) (a : Prop) : (a \/ b) = (term257 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6986750 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) (_92999 : _128167 -> nat) : (term302 _128167 _92999 _93000 _93001) = (term303 _128167 _93000 _93001 _92999).
Proof. exact (@lem6986749 (term191 _128167 _93000 _93001) ((term194 _128167 _93000 _93001 _92999) = (term78 _128167 _93000 _93001 _92999))). Qed.
Lemma lem6986752 (a : Prop) (b : Prop) : (term259 a b) = (term260 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6986753 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : (term304 _128167 _93000 _93001) = (term305 _128167 _93000 _93001).
Proof. exact (@lem6986752 (term219 _128167 _93000) (term188 _128167 _93000 _93001)). Qed.
Lemma lem6986755 (a : Prop) : (term263 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6986756 {_128167 : Type'} (_93000 : _128167 -> Prop) : (term264 _128167 _93000) = (@FINITE _128167 _93000).
Proof. exact (@lem6986755 (@FINITE _128167 _93000)). Qed.
Lemma lem6986757 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6986758 {_128167 : Type'} (_93000 : _128167 -> Prop) : (term265 _128167 _93000) = (term266 _128167 _93000).
Proof. exact (MK_COMB (@lem6986757) (@lem6986756 _128167 _93000)). Qed.
Lemma lem6986760 (a : Prop) (b : Prop) : (term259 a b) = (term260 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6986761 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : (term306 _128167 _93000 _93001) = (term307 _128167 _93000 _93001).
Proof. exact (@lem6986760 (term219 _128167 _93001) (term224 _128167 _93000 _93001)). Qed.
Lemma lem6986763 (a : Prop) : (term263 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6986764 {_128167 : Type'} (_93001 : _128167 -> Prop) : (term264 _128167 _93001) = (@FINITE _128167 _93001).
Proof. exact (@lem6986763 (@FINITE _128167 _93001)). Qed.
Lemma lem6986765 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6986766 {_128167 : Type'} (_93001 : _128167 -> Prop) : (term265 _128167 _93001) = (term266 _128167 _93001).
Proof. exact (MK_COMB (@lem6986765) (@lem6986764 _128167 _93001)). Qed.
Lemma lem6986768 (a : Prop) : (term263 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6986769 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : (term308 _128167 _93000 _93001) = (@DISJOINT _128167 _93000 _93001).
Proof. exact (@lem6986768 (@DISJOINT _128167 _93000 _93001)). Qed.
Lemma lem6986770 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : (term307 _128167 _93000 _93001) = (term193 _128167 _93000 _93001).
Proof. exact (MK_COMB (@lem6986766 _128167 _93001) (@lem6986769 _128167 _93000 _93001)). Qed.
Lemma lem6986771 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : (term306 _128167 _93000 _93001) = (term193 _128167 _93000 _93001).
Proof. exact (TRANS (@lem6986761 _128167 _93000 _93001) (@lem6986770 _128167 _93000 _93001)). Qed.
Lemma lem6986772 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : (term305 _128167 _93000 _93001) = (term199 _128167 _93000 _93001).
Proof. exact (MK_COMB (@lem6986758 _128167 _93000) (@lem6986771 _128167 _93000 _93001)). Qed.
Lemma lem6986773 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : (term304 _128167 _93000 _93001) = (term199 _128167 _93000 _93001).
Proof. exact (TRANS (@lem6986753 _128167 _93000 _93001) (@lem6986772 _128167 _93000 _93001)). Qed.
Lemma lem6986774 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6986775 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) : (term309 _128167 _93000 _93001) = (term310 _128167 _93000 _93001).
Proof. exact (MK_COMB (@lem6986774) (@lem6986773 _128167 _93000 _93001)). Qed.
Lemma lem6986776 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) (_92999 : _128167 -> nat) : ((term194 _128167 _93000 _93001 _92999) = (term78 _128167 _93000 _93001 _92999)) = ((term194 _128167 _93000 _93001 _92999) = (term78 _128167 _93000 _93001 _92999)).
Proof. exact (eq_refl ((term194 _128167 _93000 _93001 _92999) = (term78 _128167 _93000 _93001 _92999))). Qed.
Lemma lem6986777 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) (_92999 : _128167 -> nat) : (term303 _128167 _93000 _93001 _92999) = (term45 _128167 _93000 _93001 _92999).
Proof. exact (MK_COMB (@lem6986775 _128167 _93000 _93001) (@lem6986776 _128167 _93000 _93001 _92999)). Qed.
Lemma lem6986778 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) (_92999 : _128167 -> nat) : (term302 _128167 _92999 _93000 _93001) = (term45 _128167 _93000 _93001 _92999).
Proof. exact (TRANS (@lem6986750 _128167 _93000 _93001 _92999) (@lem6986777 _128167 _93000 _93001 _92999)). Qed.
Lemma lem6986780 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term13 _128167) (h3 : term14 _128167) (h4 : term76 _128167 s t u f) : term193 _128167 s t.
Proof. exact (conj (@lem6986518 _128167 s t u f h2 h3 h4) (@lem6986551 _128167 s t u f h1 h4)). Qed.
Lemma lem6986781 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term13 _128167) (h3 : term14 _128167) (h4 : term76 _128167 s t u f) : term199 _128167 s t.
Proof. exact (conj (@lem6986489 _128167 s t u f h2 h3 h4) (@lem6986780 _128167 s t u f h1 h2 h3 h4)). Qed.
Lemma lem6986783 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) (_92999 : _128167 -> nat) (h1 : term11 _128167) : term45 _128167 _93000 _93001 _92999.
Proof. exact (EQ_MP (@lem6986778 _128167 _93000 _93001 _92999) (@lem6986747 _128167 _92999 _93000 _93001 h1)). Qed.
Lemma lem6986784 {_128167 : Type'} (_93000 : _128167 -> Prop) (_93001 : _128167 -> Prop) (_92999 : _128167 -> nat) (h1 : term11 _128167) : term45 _128167 _93000 _93001 _92999.
Proof. exact (@lem6986783 _128167 _93000 _93001 _92999 h1). Qed.
Lemma lem6986785 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (_92999 : _128167 -> nat) (h1 : term11 _128167) : term45 _128167 s t _92999.
Proof. exact (@lem6986784 _128167 s t _92999 h1). Qed.
Lemma lem6986788 {_128167 : Type'} (_92999 : _128167 -> nat) (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term13 _128167) (h3 : term11 _128167) (h4 : term14 _128167) (h5 : term76 _128167 s t u f) : (term194 _128167 s t _92999) = (term78 _128167 s t _92999).
Proof. exact (@lem6986785 _128167 s t _92999 h3 (@lem6986781 _128167 s t u f h1 h2 h4 h5)). Qed.
Lemma lem6986789 {_128167 : Type'} (_92999 : _128167 -> nat) (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term13 _128167) (h3 : term11 _128167) (h4 : term14 _128167) (h5 : term76 _128167 s t u f) : (term194 _128167 s t _92999) = (term78 _128167 s t _92999).
Proof. exact (@lem6986788 _128167 _92999 s t u f h1 h2 h3 h4 h5). Qed.
Lemma lem6986790 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term13 _128167) (h3 : term11 _128167) (h4 : term14 _128167) (h5 : term76 _128167 s t u f) : (term194 _128167 s t f) = (term78 _128167 s t f).
Proof. exact (@lem6986789 _128167 f s t u f h1 h2 h3 h4 h5). Qed.
Lemma lem6986791 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term13 _128167) (h3 : term11 _128167) (h4 : term14 _128167) (h5 : term76 _128167 s t u f) : term311 _128167 s t f.
Proof. exact (fun h0 : term312 _128167 s t f => @lem6986790 _128167 s t u f h1 h2 h3 h4 h5). Qed.
Lemma lem6986793 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6986794 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : (term311 _128167 s t f) = ((term194 _128167 s t f) = (term78 _128167 s t f)).
Proof. exact (@lem6986793 ((term194 _128167 s t f) = (term78 _128167 s t f))). Qed.
Lemma lem6986795 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term13 _128167) (h3 : term11 _128167) (h4 : term14 _128167) (h5 : term76 _128167 s t u f) : (term194 _128167 s t f) = (term78 _128167 s t f).
Proof. exact (EQ_MP (@lem6986794 _128167 s t f) (@lem6986791 _128167 s t u f h1 h2 h3 h4 h5)). Qed.
Lemma lem6986797 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem6986798 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : (term194 _128167 s t f) = (term194 _128167 s t f).
Proof. exact (@lem6986797 (term194 _128167 s t f)). Qed.
Lemma lem6986799 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : term313 _128167 s t f.
Proof. exact (fun h0 : term314 _128167 s t f => @lem6986798 _128167 s t f). Qed.
Lemma lem6986801 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6986802 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : (term313 _128167 s t f) = ((term194 _128167 s t f) = (term194 _128167 s t f)).
Proof. exact (@lem6986801 ((term194 _128167 s t f) = (term194 _128167 s t f))). Qed.
Lemma lem6986803 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : (term194 _128167 s t f) = (term194 _128167 s t f).
Proof. exact (EQ_MP (@lem6986802 _128167 s t f) (@lem6986799 _128167 s t f)). Qed.
Lemma lem6986821 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6986822 (y : nat) (x : nat) (z : nat) : (term315 x y z) = (term316 y x z).
Proof. exact (@lem6986821 (y = z) (term317 x z)). Qed.
Lemma lem6986832 (x : nat) (y : nat) : (term318 x y) = (term318 x y).
Proof. exact (eq_refl (term318 x y)). Qed.
Lemma lem6986833 (y : nat) (x : nat) (z : nat) : (term245 x y z) = (term319 y x z).
Proof. exact (MK_COMB (@lem6986832 x y) (@lem6986822 y x z)). Qed.
Lemma lem6986837 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6986838 (y : nat) (x : nat) (z : nat) : (term319 y x z) = (term320 y x z).
Proof. exact (@lem6986837 (y = z) (term317 x y) (term317 x z)). Qed.
Lemma lem6986860 (y : nat) (x : nat) (z : nat) : (term245 x y z) = (term320 y x z).
Proof. exact (TRANS (@lem6986833 y x z) (@lem6986838 y x z)). Qed.
Lemma lem6986861 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6986862 (y : nat) (x : nat) (z : nat) : (term321 x y z) = (term322 y x z).
Proof. exact (MK_COMB (@lem6986861) (@lem6986860 y x z)). Qed.
Lemma lem6986884 (y : nat) (x : nat) (z : nat) : (term320 y x z) = (term320 y x z).
Proof. exact (eq_refl (term320 y x z)). Qed.
Lemma lem6986885 (y : nat) (x : nat) (z : nat) : ((term245 x y z) = (term320 y x z)) = ((term320 y x z) = (term320 y x z)).
Proof. exact (MK_COMB (@lem6986862 y x z) (@lem6986884 y x z)). Qed.
Lemma lem6986887 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6986888 (x : Prop) : (x = x) = True.
Proof. exact (@lem6986887 Prop x). Qed.
Lemma lem6986889 (y : nat) (x : nat) (z : nat) : ((term320 y x z) = (term320 y x z)) = True.
Proof. exact (@lem6986888 (term320 y x z)). Qed.
Lemma lem6986890 (y : nat) (x : nat) (z : nat) : ((term245 x y z) = (term320 y x z)) = True.
Proof. exact (TRANS (@lem6986885 y x z) (@lem6986889 y x z)). Qed.
Lemma lem6986891 (y : nat) (x : nat) (z : nat) : True = ((term245 x y z) = (term320 y x z)).
Proof. exact (SYM (@lem6986890 y x z)). Qed.
Lemma lem6986892 (y : nat) (x : nat) (z : nat) : (term245 x y z) = (term320 y x z).
Proof. exact (EQ_MP (@lem6986891 y x z) (@lem0)). Qed.
Lemma lem6986893 (y : nat) (x : nat) (z : nat) : term320 y x z.
Proof. exact (EQ_MP (@lem6986892 y x z) (@lem6986358 x y z)). Qed.
Lemma lem6986895 (b : Prop) (a : Prop) : (a \/ b) = (term257 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6986896 (x : nat) (y : nat) (z : nat) : (term320 y x z) = (term323 x y z).
Proof. exact (@lem6986895 (term324 y x z) (y = z)). Qed.
Lemma lem6986898 (a : Prop) (b : Prop) : (term259 a b) = (term260 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6986899 (y : nat) (x : nat) (z : nat) : (term325 y x z) = (term326 y x z).
Proof. exact (@lem6986898 (term317 x y) (term317 x z)). Qed.
Lemma lem6986901 (a : Prop) : (term263 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6986902 (x : nat) (y : nat) : (term327 x y) = (x = y).
Proof. exact (@lem6986901 (x = y)). Qed.
Lemma lem6986903 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6986904 (x : nat) (y : nat) : (term328 x y) = (term329 x y).
Proof. exact (MK_COMB (@lem6986903) (@lem6986902 x y)). Qed.
Lemma lem6986906 (a : Prop) : (term263 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6986907 (x : nat) (z : nat) : (term327 x z) = (x = z).
Proof. exact (@lem6986906 (x = z)). Qed.
Lemma lem6986908 (y : nat) (x : nat) (z : nat) : (term326 y x z) = (term330 y x z).
Proof. exact (MK_COMB (@lem6986904 x y) (@lem6986907 x z)). Qed.
Lemma lem6986909 (y : nat) (x : nat) (z : nat) : (term325 y x z) = (term330 y x z).
Proof. exact (TRANS (@lem6986899 y x z) (@lem6986908 y x z)). Qed.
Lemma lem6986910 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6986911 (y : nat) (x : nat) (z : nat) : (term331 y x z) = (term332 y x z).
Proof. exact (MK_COMB (@lem6986910) (@lem6986909 y x z)). Qed.
Lemma lem6986912 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem6986913 (x : nat) (y : nat) (z : nat) : (term323 x y z) = (term333 x y z).
Proof. exact (MK_COMB (@lem6986911 y x z) (@lem6986912 y z)). Qed.
Lemma lem6986914 (x : nat) (y : nat) (z : nat) : (term320 y x z) = (term333 x y z).
Proof. exact (TRANS (@lem6986896 x y z) (@lem6986913 x y z)). Qed.
Lemma lem6986916 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term13 _128167) (h3 : term11 _128167) (h4 : term14 _128167) (h5 : term76 _128167 s t u f) : term334 _128167 s t f.
Proof. exact (conj (@lem6986795 _128167 s t u f h1 h2 h3 h4 h5) (@lem6986803 _128167 s t f)). Qed.
Lemma lem6986918 (x : nat) (y : nat) (z : nat) : term333 x y z.
Proof. exact (EQ_MP (@lem6986914 x y z) (@lem6986893 y x z)). Qed.
Lemma lem6986919 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : term335 _128167 s t f.
Proof. exact (@lem6986918 (term194 _128167 s t f) (term78 _128167 s t f) (term194 _128167 s t f)). Qed.
Lemma lem6986922 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term13 _128167) (h3 : term11 _128167) (h4 : term14 _128167) (h5 : term76 _128167 s t u f) : (term78 _128167 s t f) = (term194 _128167 s t f).
Proof. exact (@lem6986919 _128167 s t f (@lem6986916 _128167 s t u f h1 h2 h3 h4 h5)). Qed.
Lemma lem6986923 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term13 _128167) (h3 : term11 _128167) (h4 : term14 _128167) (h5 : term76 _128167 s t u f) : term336 _128167 s t f.
Proof. exact (fun h0 : term230 _128167 s t f => @lem6986922 _128167 s t u f h1 h2 h3 h4 h5). Qed.
Lemma lem6986925 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6986926 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : (term336 _128167 s t f) = ((term78 _128167 s t f) = (term194 _128167 s t f)).
Proof. exact (@lem6986925 ((term78 _128167 s t f) = (term194 _128167 s t f))). Qed.
Lemma lem6986927 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term13 _128167) (h3 : term11 _128167) (h4 : term14 _128167) (h5 : term76 _128167 s t u f) : (term78 _128167 s t f) = (term194 _128167 s t f).
Proof. exact (EQ_MP (@lem6986926 _128167 s t f) (@lem6986923 _128167 s t u f h1 h2 h3 h4 h5)). Qed.
Lemma lem6986930 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6986932 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) : (term230 _128167 s t f) = (term337 _128167 s t f).
Proof. exact (@lem6986930 ((term78 _128167 s t f) = (term194 _128167 s t f))). Qed.
Lemma lem6986935 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term76 _128167 s t u f) : term337 _128167 s t f.
Proof. exact (EQ_MP (@lem6986932 _128167 s t f) (@lem6986027 _128167 s t u f h1)). Qed.
Lemma lem6986938 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term13 _128167) (h3 : term11 _128167) (h4 : term14 _128167) (h5 : term76 _128167 s t u f) : False.
Proof. exact (@lem6986935 _128167 s t u f h5 (@lem6986927 _128167 s t u f h1 h2 h3 h4 h5)). Qed.
Lemma lem6986939 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term13 _128167) (h3 : term11 _128167) (h4 : term14 _128167) (h5 : term76 _128167 s t u f) : term338.
Proof. exact (fun h0 : ~ False => @lem6986938 _128167 s t u f h1 h2 h3 h4 h5). Qed.
Lemma lem6986941 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6986942 : term338 = False.
Proof. exact (@lem6986941 False). Qed.
Lemma lem6986945 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term13 _128167) (h3 : term11 _128167) (h4 : term14 _128167) (h5 : term76 _128167 s t u f) : False.
Proof. exact (EQ_MP (@lem6986942) (@lem6986939 _128167 s t u f h1 h2 h3 h4 h5)). Qed.
Lemma lem6986946 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term13 _128167) (h3 : term11 _128167) (h4 : term14 _128167) (h5 : term76 _128167 s t u f) : (term76 _128167 s t u f) = False.
Proof. exact (prop_ext (fun h6 : term76 _128167 s t u f => @lem6986945 _128167 s t u f h1 h2 h3 h4 h5) (fun h6 : False => @lem6985249 _128167 s t u f h5)). Qed.
Lemma lem6986947 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term13 _128167) (h3 : term11 _128167) (h4 : term14 _128167) (h5 : term76 _128167 s t u f) : False.
Proof. exact (EQ_MP (@lem6986946 _128167 s t u f h1 h2 h3 h4 h5) (@lem6985249 _128167 s t u f h5)). Qed.
Lemma lem6986948 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term13 _128167) (h3 : term11 _128167) (h4 : term14 _128167) (h5 : term76 _128167 s t u f) : (term14 _128167) = False.
Proof. exact (prop_ext (fun h6 : term14 _128167 => @lem6986947 _128167 s t u f h1 h2 h3 h4 h5) (fun h6 : False => @lem6984909 _128167 h4)). Qed.
Lemma lem6986949 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (u : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term13 _128167) (h3 : term11 _128167) (h4 : term14 _128167) (h5 : term76 _128167 s t u f) : False.
Proof. exact (EQ_MP (@lem6986948 _128167 s t u f h1 h2 h3 h4 h5) (@lem6984909 _128167 h4)). Qed.
Lemma lem6986950 {_128167 : Type'} (s : _128167 -> Prop) (t : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term13 _128167) (h3 : term11 _128167) (h4 : term87 _128167 s t f) (h5 : term14 _128167) : False.
Proof. exact (ex_elim (@lem6984840 _128167 s t f h4) (fun u : _128167 -> Prop => fun h0 : term86 _128167 s t f u => @lem6986949 _128167 s t u f h1 h2 h3 h5 h0)). Qed.
Lemma lem6986951 {_128167 : Type'} (s : _128167 -> Prop) (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term13 _128167) (h3 : term11 _128167) (h4 : term94 _128167 s f) (h5 : term14 _128167) : False.
Proof. exact (ex_elim (@lem6984839 _128167 s f h4) (fun t : _128167 -> Prop => fun h0 : term93 _128167 s f t => @lem6986950 _128167 s t f h1 h2 h3 h0 h5)). Qed.
Lemma lem6986952 {_128167 : Type'} (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term13 _128167) (h3 : term11 _128167) (h4 : term10 _128167 f) (h5 : term14 _128167) : False.
Proof. exact (ex_elim (@lem6983702 _128167 f h4) (fun s : _128167 -> Prop => fun h0 : term99 _128167 f s => @lem6986951 _128167 s f h1 h2 h3 h0 h5)). Qed.
Lemma lem6986953 {_128167 : Type'} (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term13 _128167) (h3 : term11 _128167) (h4 : term10 _128167 f) (h5 : term14 _128167) : (term14 _128167) = False.
Proof. exact (prop_ext (fun h6 : term14 _128167 => @lem6986952 _128167 f h1 h2 h3 h4 h5) (fun h6 : False => @lem6983778 _128167 h5)). Qed.
Lemma lem6986954 {_128167 : Type'} (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term13 _128167) (h3 : term11 _128167) (h4 : term10 _128167 f) (h5 : term14 _128167) : False.
Proof. exact (EQ_MP (@lem6986953 _128167 f h1 h2 h3 h4 h5) (@lem6983778 _128167 h5)). Qed.
Lemma lem6986955 {_128167 : Type'} (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term13 _128167) (h3 : term10 _128167 f) (h4 : term14 _128167) : term19 _128167.
Proof. exact (fun h0 : term11 _128167 => @lem6986954 _128167 f h1 h2 h0 h3 h4). Qed.
Lemma lem6986956 {_128167 : Type'} : (term19 _128167) = (term20 _128167).
Proof. exact (@lem69 (term11 _128167)). Qed.
Lemma lem6986957 {_128167 : Type'} (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term13 _128167) (h3 : term10 _128167 f) (h4 : term14 _128167) : term20 _128167.
Proof. exact (EQ_MP (@lem6986956 _128167) (@lem6986955 _128167 f h1 h2 h3 h4)). Qed.
Lemma lem6986958 {_126551 _128167 : Type'} (f : _128167 -> nat) (h1 : term12 _128167) (h2 : term13 _128167) (h3 : term10 _128167 f) (h4 : term14 _128167) : term23 _126551 _128167.
Proof. exact (fun h0 : term11 _126551 => @lem6986957 _128167 f h1 h2 h3 h4). Qed.
Lemma lem6986959 {_126551 _128167 : Type'} (f : _128167 -> nat) (h1 : term13 _128167) (h2 : term10 _128167 f) (h3 : term14 _128167) : term26 _126551 _128167.
Proof. exact (fun h0 : term12 _128167 => @lem6986958 _126551 _128167 f h0 h1 h2 h3). Qed.
Lemma lem6986960 {_126551 _128167 : Type'} (f : _128167 -> nat) (h1 : term13 _128167) (h2 : term10 _128167 f) (h3 : term14 _128167) : term28 _126551 _128167.
Proof. exact (fun h0 : term12 _126551 => @lem6986959 _126551 _128167 f h1 h2 h3). Qed.
Lemma lem6986961 {_126551 _128167 : Type'} (f : _128167 -> nat) (h1 : term10 _128167 f) (h2 : term14 _128167) : term31 _126551 _128167.
Proof. exact (fun h0 : term13 _128167 => @lem6986960 _126551 _128167 f h0 h1 h2). Qed.
Lemma lem6986962 {_126551 _128167 : Type'} (f : _128167 -> nat) (h1 : term10 _128167 f) (h2 : term14 _128167) : term33 _126551 _128167.
Proof. exact (fun h0 : term13 _126551 => @lem6986961 _126551 _128167 f h1 h2). Qed.
Lemma lem6986963 {_126551 _128167 : Type'} (f : _128167 -> nat) (h1 : term10 _128167 f) : term36 _126551 _128167.
Proof. exact (fun h0 : term14 _128167 => @lem6986962 _126551 _128167 f h1 h0). Qed.
Lemma lem6986964 {_126551 _128167 : Type'} (f : _128167 -> nat) (h1 : term10 _128167 f) : term38 _126551 _128167.
Proof. exact (fun h0 : term14 _126551 => @lem6986963 _126551 _128167 f h1). Qed.
Lemma lem6986965 {_126551 _128167 : Type'} (f : _128167 -> nat) : term40 _126551 _128167 f.
Proof. exact (fun h0 : term10 _128167 f => @lem6986964 _126551 _128167 f h0). Qed.
Lemma lem6986970 {_126551 _128167 : Type'} : term44 _126551 _128167.
Proof. exact (fun f : _128167 -> nat => @lem6986965 _126551 _128167 f). Qed.
Lemma lem6986971 {_126551 _128167 : Type'} : term43 _126551 _128167.
Proof. exact (EQ_MP (@lem6983587 _126551 _128167) (@lem6986970 _126551 _128167)). Qed.
Lemma lem6986972 {_126551 _128167 : Type'} (f : _128167 -> nat) : term339 _126551 _128167 f.
Proof. exact (@lem6986971 _126551 _128167 f). Qed.
Lemma lem6986973 {_126551 _128167 : Type'} (f : _128167 -> nat) : (term339 _126551 _128167 f) = (term15 _126551 _128167 f).
Proof. exact (eq_refl (term339 _126551 _128167 f)). Qed.
Lemma lem6986974 {_126551 _128167 : Type'} (f : _128167 -> nat) : term15 _126551 _128167 f.
Proof. exact (EQ_MP (@lem6986973 _126551 _128167 f) (@lem6986972 _126551 _128167 f)). Qed.
Lemma lem6986976 {_126551 _128167 : Type'} (f : _128167 -> nat) : term15 _126551 _128167 f.
Proof. exact (@lem6983002 _126551 _128167 f (@lem6986974 _126551 _128167 f)). Qed.
Lemma lem6986977 {_126551 _128167 : Type'} (f : _128167 -> nat) (h1 : term10 _128167 f) : term37 _126551 _128167.
Proof. exact (@lem6986976 _126551 _128167 f (@lem6982972 _128167 f h1)). Qed.
Lemma lem6986978 {_126551 _128167 : Type'} (f : _128167 -> nat) (h1 : term10 _128167 f) : term35 _126551 _128167.
Proof. exact (@lem6986977 _126551 _128167 f h1 (@lem6982984 _126551)). Qed.
Lemma lem6986979 {_126551 _128167 : Type'} (f : _128167 -> nat) (h1 : term10 _128167 f) : term32 _126551 _128167.
Proof. exact (@lem6986978 _126551 _128167 f h1 (@lem6982983 _128167)). Qed.
Lemma lem6986980 {_126551 _128167 : Type'} (f : _128167 -> nat) (h1 : term10 _128167 f) : term30 _126551 _128167.
Proof. exact (@lem6986979 _126551 _128167 f h1 (@lem6982982 _126551)). Qed.
Lemma lem6986981 {_126551 _128167 : Type'} (f : _128167 -> nat) (h1 : term10 _128167 f) : term27 _126551 _128167.
Proof. exact (@lem6986980 _126551 _128167 f h1 (@lem6982981 _128167)). Qed.
Lemma lem6986982 {_126551 _128167 : Type'} (f : _128167 -> nat) (h1 : term10 _128167 f) : term25 _126551 _128167.
Proof. exact (@lem6986981 _126551 _128167 f h1 (@lem6982977 _126551)). Qed.
Lemma lem6986983 {_126551 _128167 : Type'} (f : _128167 -> nat) (h1 : term10 _128167 f) : term22 _126551 _128167.
Proof. exact (@lem6986982 _126551 _128167 f h1 (@lem6982976 _128167)). Qed.
Lemma lem6986984 {_128167 : Type'} (f : _128167 -> nat) (h1 : term10 _128167 f) : term19 _128167.
Proof. exact (@lem6986983 Prop _128167 f h1 (@lem6925097 Prop)). Qed.
Lemma lem6986985 {_128167 : Type'} (f : _128167 -> nat) (h1 : term10 _128167 f) : False.
Proof. exact (@lem6986984 _128167 f h1 (@lem6982973 _128167)). Qed.
Lemma lem6986986 {_128167 : Type'} (f : _128167 -> nat) (h1 : term10 _128167 f) : (term10 _128167 f) = False.
Proof. exact (prop_ext (fun h2 : term10 _128167 f => @lem6986985 _128167 f h1) (fun h2 : False => @lem6982972 _128167 f h1)). Qed.
Lemma lem6986987 {_128167 : Type'} (f : _128167 -> nat) (h1 : term10 _128167 f) : False.
Proof. exact (EQ_MP (@lem6986986 _128167 f h1) (@lem6982972 _128167 f h1)). Qed.
Lemma lem6986988 {_128167 : Type'} (f : _128167 -> nat) : term9 _128167 f.
Proof. exact (fun h0 : term10 _128167 f => @lem6986987 _128167 f h0). Qed.
Lemma lem6986989 {_128167 : Type'} (f : _128167 -> nat) : term8 _128167 f.
Proof. exact (EQ_MP (@lem6982971 _128167 f) (@lem6986988 _128167 f)). Qed.
