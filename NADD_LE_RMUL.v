Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_LE_RMUL_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import NADD_LE_LMUL_spec.
Require Import NADD_LE_WELLDEF_spec.
Require Import NADD_MUL_SYM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm19490_spec.
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
Require Import thm69_spec.
Lemma lem1280017 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1280018 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1280019 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1280018 t1) (@lem1280017 t1)). Qed.
Lemma lem1280020 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1280019 t1 t2). Qed.
Lemma lem1280021 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1280022 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1280021 t1 t2) (@lem1280020 t1 t2)). Qed.
Lemma lem1280023 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1280022 t1 t2 t3). Qed.
Lemma lem1280024 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1280025 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1280024 t1 t2 t3) (@lem1280023 t1 t2 t3)). Qed.
Lemma lem1280026 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1280025 t1 t2 t3)). Qed.
Lemma lem1280028 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1280029 : term8 = term9.
Proof. exact (@lem1280028 term8). Qed.
Lemma lem1280030 : term9 = term8.
Proof. exact (SYM (@lem1280029)). Qed.
Lemma lem1280031 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1280034 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1280035 : term12.
Proof. exact (fun h0 : term11 => @lem1280034 h0). Qed.
Lemma lem1280036 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1280037 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1280038 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1280036 h2 (@lem1280037 h1)). Qed.
Lemma lem1280039 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem1280038 h1 h0). Qed.
Lemma lem1280040 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1280041 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1280039 h1 (@lem1280040 h2)). Qed.
Lemma lem1280042 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem1280041 h0 h1). Qed.
Lemma lem1280043 : term14.
Proof. exact (fun h0 : term12 => @lem1280042 h0). Qed.
Lemma lem1280046 : term12.
Proof. exact (@lem1280043 (@lem1280035)). Qed.
Lemma lem1280096 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1280097 : term15 = term16.
Proof. exact (@lem1280096 term17). Qed.
Lemma lem1280112 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1280113 : term19 = term20.
Proof. exact (MK_COMB (@lem1280112) (@lem1280097)). Qed.
Lemma lem1280116 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1280117 : term22 = term23.
Proof. exact (MK_COMB (@lem1280116) (@lem1280113)). Qed.
Lemma lem1280120 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1280127 : term11 = term25.
Proof. exact (MK_COMB (@lem1280120) (@lem1280117)). Qed.
Lemma lem1280132 (y : nadd) (x : nadd) (z : nadd) : (term26 y x z) = (term26 y x z).
Proof. exact (eq_refl (term26 y x z)). Qed.
Lemma lem1280133 (y : nadd) (x : nadd) : (term27 y x) = (term27 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1280132 y x z)). Qed.
Lemma lem1280134 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280135 (y : nadd) (x : nadd) : (term28 y x) = (term28 y x).
Proof. exact (MK_COMB (@lem1280134) (@lem1280133 y x)). Qed.
Lemma lem1280136 (x : nadd) : (term29 x) = (term29 x).
Proof. exact (fun_ext (fun y : nadd => @lem1280135 y x)). Qed.
Lemma lem1280137 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280138 (x : nadd) : (term30 x) = (term30 x).
Proof. exact (MK_COMB (@lem1280137) (@lem1280136 x)). Qed.
Lemma lem1280139 : term31 = term31.
Proof. exact (fun_ext (fun x : nadd => @lem1280138 x)). Qed.
Lemma lem1280140 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280141 : term17 = term17.
Proof. exact (MK_COMB (@lem1280140) (@lem1280139)). Qed.
Lemma lem1280142 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1280143 : term16 = term16.
Proof. exact (MK_COMB (@lem1280142) (@lem1280141)). Qed.
Lemma lem1280156 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term32 x y x' y') = (term32 x y x' y').
Proof. exact (eq_refl (term32 x y x' y')). Qed.
Lemma lem1280157 (x : nadd) (y : nadd) (x' : nadd) : (term33 x y x') = (term33 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1280156 x y x' y')). Qed.
Lemma lem1280158 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280159 (x : nadd) (y : nadd) (x' : nadd) : (term34 x y x') = (term34 x y x').
Proof. exact (MK_COMB (@lem1280158) (@lem1280157 x y x')). Qed.
Lemma lem1280160 (x : nadd) (x' : nadd) : (term35 x x') = (term35 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1280159 x y x')). Qed.
Lemma lem1280161 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280162 (x : nadd) (x' : nadd) : (term36 x x') = (term36 x x').
Proof. exact (MK_COMB (@lem1280161) (@lem1280160 x x')). Qed.
Lemma lem1280163 (x : nadd) : (term37 x) = (term37 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1280162 x x')). Qed.
Lemma lem1280164 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280165 (x : nadd) : (term38 x) = (term38 x).
Proof. exact (MK_COMB (@lem1280164) (@lem1280163 x)). Qed.
Lemma lem1280166 : term39 = term39.
Proof. exact (fun_ext (fun x : nadd => @lem1280165 x)). Qed.
Lemma lem1280167 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280168 : term40 = term40.
Proof. exact (MK_COMB (@lem1280167) (@lem1280166)). Qed.
Lemma lem1280169 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1280170 : term18 = term18.
Proof. exact (MK_COMB (@lem1280169) (@lem1280168)). Qed.
Lemma lem1280171 : term20 = term20.
Proof. exact (MK_COMB (@lem1280170) (@lem1280143)). Qed.
Lemma lem1280172 (y : nadd) (x : nadd) : (term41 y x) = (term41 y x).
Proof. exact (eq_refl (term41 y x)). Qed.
Lemma lem1280173 (x : nadd) : (term42 x) = (term42 x).
Proof. exact (fun_ext (fun y : nadd => @lem1280172 y x)). Qed.
Lemma lem1280174 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280175 (x : nadd) : (term43 x) = (term43 x).
Proof. exact (MK_COMB (@lem1280174) (@lem1280173 x)). Qed.
Lemma lem1280176 : term44 = term44.
Proof. exact (fun_ext (fun x : nadd => @lem1280175 x)). Qed.
Lemma lem1280177 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280178 : term45 = term45.
Proof. exact (MK_COMB (@lem1280177) (@lem1280176)). Qed.
Lemma lem1280179 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1280180 : term21 = term21.
Proof. exact (MK_COMB (@lem1280179) (@lem1280178)). Qed.
Lemma lem1280181 : term23 = term23.
Proof. exact (MK_COMB (@lem1280180) (@lem1280171)). Qed.
Lemma lem1280186 (x : nadd) (y : nadd) (z : nadd) : (term46 x y z) = (term46 x y z).
Proof. exact (eq_refl (term46 x y z)). Qed.
Lemma lem1280187 (x : nadd) (y : nadd) : (term47 x y) = (term47 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1280186 x y z)). Qed.
Lemma lem1280188 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280189 (x : nadd) (y : nadd) : (term48 x y) = (term48 x y).
Proof. exact (MK_COMB (@lem1280188) (@lem1280187 x y)). Qed.
Lemma lem1280190 (x : nadd) : (term49 x) = (term49 x).
Proof. exact (fun_ext (fun y : nadd => @lem1280189 x y)). Qed.
Lemma lem1280191 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280192 (x : nadd) : (term50 x) = (term50 x).
Proof. exact (MK_COMB (@lem1280191) (@lem1280190 x)). Qed.
Lemma lem1280193 : term51 = term51.
Proof. exact (fun_ext (fun x : nadd => @lem1280192 x)). Qed.
Lemma lem1280194 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280195 : term8 = term8.
Proof. exact (MK_COMB (@lem1280194) (@lem1280193)). Qed.
Lemma lem1280196 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1280197 : term10 = term10.
Proof. exact (MK_COMB (@lem1280196) (@lem1280195)). Qed.
Lemma lem1280198 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1280199 : term24 = term24.
Proof. exact (MK_COMB (@lem1280198) (@lem1280197)). Qed.
Lemma lem1280200 : term25 = term25.
Proof. exact (MK_COMB (@lem1280199) (@lem1280181)). Qed.
Lemma lem1280289 : term11 = term25.
Proof. exact (TRANS (@lem1280127) (@lem1280200)). Qed.
Lemma lem1280290 : term25 = term11.
Proof. exact (SYM (@lem1280289)). Qed.
Lemma lem1280291 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1280292 (h1 : term45) : term45.
Proof. exact (h1). Qed.
Lemma lem1280293 (h1 : term40) : term40.
Proof. exact (h1). Qed.
Lemma lem1280294 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1280301 (x : nadd) (y : nadd) (z : nadd) : (term52 x y z) = (term53 x y z).
Proof. exact (@lem17362 (nadd_le x y) (term54 x y z)). Qed.
Lemma lem1280302 (P : nadd -> Prop) : (term55 P) = (term56 P).
Proof. exact (@lem18392 nadd P). Qed.
Lemma lem1280303 (x : nadd) (y : nadd) : (term57 x y) = (term58 x y).
Proof. exact (@lem1280302 (term47 x y)). Qed.
Lemma lem1280304 (x : nadd) (y : nadd) (z : nadd) : (term59 x y z) = (term46 x y z).
Proof. exact (eq_refl (term59 x y z)). Qed.
Lemma lem1280305 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1280306 (x : nadd) (y : nadd) (z : nadd) : (term60 x y z) = (term52 x y z).
Proof. exact (MK_COMB (@lem1280305) (@lem1280304 x y z)). Qed.
Lemma lem1280307 (x : nadd) (y : nadd) (z : nadd) : (term60 x y z) = (term53 x y z).
Proof. exact (TRANS (@lem1280306 x y z) (@lem1280301 x y z)). Qed.
Lemma lem1280308 (x : nadd) (y : nadd) : (term61 x y) = (term62 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1280307 x y z)). Qed.
Lemma lem1280309 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1280310 (x : nadd) (y : nadd) : (term58 x y) = (term63 x y).
Proof. exact (MK_COMB (@lem1280309) (@lem1280308 x y)). Qed.
Lemma lem1280311 (x : nadd) (y : nadd) : (term57 x y) = (term63 x y).
Proof. exact (TRANS (@lem1280303 x y) (@lem1280310 x y)). Qed.
Lemma lem1280312 (P : nadd -> Prop) : (term55 P) = (term56 P).
Proof. exact (@lem18392 nadd P). Qed.
Lemma lem1280313 (x : nadd) : (term64 x) = (term65 x).
Proof. exact (@lem1280312 (term49 x)). Qed.
Lemma lem1280314 (x : nadd) (y : nadd) : (term66 x y) = (term48 x y).
Proof. exact (eq_refl (term66 x y)). Qed.
Lemma lem1280315 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1280316 (x : nadd) (y : nadd) : (term67 x y) = (term57 x y).
Proof. exact (MK_COMB (@lem1280315) (@lem1280314 x y)). Qed.
Lemma lem1280317 (x : nadd) (y : nadd) : (term67 x y) = (term63 x y).
Proof. exact (TRANS (@lem1280316 x y) (@lem1280311 x y)). Qed.
Lemma lem1280318 (x : nadd) : (term68 x) = (term69 x).
Proof. exact (fun_ext (fun y : nadd => @lem1280317 x y)). Qed.
Lemma lem1280319 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1280320 (x : nadd) : (term65 x) = (term70 x).
Proof. exact (MK_COMB (@lem1280319) (@lem1280318 x)). Qed.
Lemma lem1280321 (x : nadd) : (term64 x) = (term70 x).
Proof. exact (TRANS (@lem1280313 x) (@lem1280320 x)). Qed.
Lemma lem1280322 (P : nadd -> Prop) : (term55 P) = (term56 P).
Proof. exact (@lem18392 nadd P). Qed.
Lemma lem1280323 : term10 = term71.
Proof. exact (@lem1280322 term51). Qed.
Lemma lem1280324 (x : nadd) : (term72 x) = (term50 x).
Proof. exact (eq_refl (term72 x)). Qed.
Lemma lem1280325 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1280326 (x : nadd) : (term73 x) = (term64 x).
Proof. exact (MK_COMB (@lem1280325) (@lem1280324 x)). Qed.
Lemma lem1280327 (x : nadd) : (term73 x) = (term70 x).
Proof. exact (TRANS (@lem1280326 x) (@lem1280321 x)). Qed.
Lemma lem1280328 : term74 = term75.
Proof. exact (fun_ext (fun x : nadd => @lem1280327 x)). Qed.
Lemma lem1280329 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1280330 : term71 = term76.
Proof. exact (MK_COMB (@lem1280329) (@lem1280328)). Qed.
Lemma lem1280331 : term10 = term76.
Proof. exact (TRANS (@lem1280323) (@lem1280330)). Qed.
Lemma lem1280341 {A : Type'} (P : Prop) (Q : A -> Prop) : (term77 A P Q) = (term78 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem1280342 (P : Prop) (Q : nadd -> Prop) : (term79 P Q) = (term80 P Q).
Proof. exact (@lem1280341 nadd P Q). Qed.
Lemma lem1280343 (x : nadd) (y : nadd) : (term81 x y) = (term82 x y).
Proof. exact (@lem1280342 (nadd_le x y) (term83 x y)). Qed.
Lemma lem1280344 (x : nadd) (y : nadd) (z : nadd) : (term84 x y z) = (term85 x y z).
Proof. exact (eq_refl (term84 x y z)). Qed.
Lemma lem1280345 (x : nadd) (y : nadd) : (term86 x y) = (term86 x y).
Proof. exact (eq_refl (term86 x y)). Qed.
Lemma lem1280346 (x : nadd) (y : nadd) (z : nadd) : (term87 x y z) = (term53 x y z).
Proof. exact (MK_COMB (@lem1280345 x y) (@lem1280344 x y z)). Qed.
Lemma lem1280347 (x : nadd) (y : nadd) : (term88 x y) = (term62 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1280346 x y z)). Qed.
Lemma lem1280348 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1280349 (x : nadd) (y : nadd) : (term81 x y) = (term63 x y).
Proof. exact (MK_COMB (@lem1280348) (@lem1280347 x y)). Qed.
Lemma lem1280350 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1280351 (x : nadd) (y : nadd) : (term89 x y) = (term90 x y).
Proof. exact (MK_COMB (@lem1280350) (@lem1280349 x y)). Qed.
Lemma lem1280352 (x : nadd) (y : nadd) (z : nadd) : (term84 x y z) = (term85 x y z).
Proof. exact (eq_refl (term84 x y z)). Qed.
Lemma lem1280353 (x : nadd) (y : nadd) : (term91 x y) = (term83 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1280352 x y z)). Qed.
Lemma lem1280354 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1280355 (x : nadd) (y : nadd) : (term92 x y) = (term93 x y).
Proof. exact (MK_COMB (@lem1280354) (@lem1280353 x y)). Qed.
Lemma lem1280356 (x : nadd) (y : nadd) : (term86 x y) = (term86 x y).
Proof. exact (eq_refl (term86 x y)). Qed.
Lemma lem1280357 (x : nadd) (y : nadd) : (term82 x y) = (term94 x y).
Proof. exact (MK_COMB (@lem1280356 x y) (@lem1280355 x y)). Qed.
Lemma lem1280358 (x : nadd) (y : nadd) : ((term81 x y) = (term82 x y)) = ((term63 x y) = (term94 x y)).
Proof. exact (MK_COMB (@lem1280351 x y) (@lem1280357 x y)). Qed.
Lemma lem1280359 (x : nadd) (y : nadd) : (term63 x y) = (term94 x y).
Proof. exact (EQ_MP (@lem1280358 x y) (@lem1280343 x y)). Qed.
Lemma lem1280364 (x : nadd) : (term69 x) = (term95 x).
Proof. exact (fun_ext (fun y : nadd => @lem1280359 x y)). Qed.
Lemma lem1280365 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1280366 (x : nadd) : (term70 x) = (term96 x).
Proof. exact (MK_COMB (@lem1280365) (@lem1280364 x)). Qed.
Lemma lem1280415 : term75 = term97.
Proof. exact (fun_ext (fun x : nadd => @lem1280366 x)). Qed.
Lemma lem1280416 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1280417 : term76 = term98.
Proof. exact (MK_COMB (@lem1280416) (@lem1280415)). Qed.
Lemma lem1280423 {A : Type'} (P : Prop) (Q : A -> Prop) : (term78 A P Q) = (term77 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1280424 (P : Prop) (Q : nadd -> Prop) : (term80 P Q) = (term79 P Q).
Proof. exact (@lem1280423 nadd P Q). Qed.
Lemma lem1280425 (x : nadd) (y : nadd) : (term82 x y) = (term81 x y).
Proof. exact (@lem1280424 (nadd_le x y) (term83 x y)). Qed.
Lemma lem1280426 (x : nadd) (y : nadd) (z : nadd) : (term84 x y z) = (term85 x y z).
Proof. exact (eq_refl (term84 x y z)). Qed.
Lemma lem1280427 (x : nadd) (y : nadd) : (term91 x y) = (term83 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1280426 x y z)). Qed.
Lemma lem1280428 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1280429 (x : nadd) (y : nadd) : (term92 x y) = (term93 x y).
Proof. exact (MK_COMB (@lem1280428) (@lem1280427 x y)). Qed.
Lemma lem1280430 (x : nadd) (y : nadd) : (term86 x y) = (term86 x y).
Proof. exact (eq_refl (term86 x y)). Qed.
Lemma lem1280431 (x : nadd) (y : nadd) : (term82 x y) = (term94 x y).
Proof. exact (MK_COMB (@lem1280430 x y) (@lem1280429 x y)). Qed.
Lemma lem1280432 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1280433 (x : nadd) (y : nadd) : (term99 x y) = (term100 x y).
Proof. exact (MK_COMB (@lem1280432) (@lem1280431 x y)). Qed.
Lemma lem1280434 (x : nadd) (y : nadd) (z : nadd) : (term84 x y z) = (term85 x y z).
Proof. exact (eq_refl (term84 x y z)). Qed.
Lemma lem1280435 (x : nadd) (y : nadd) : (term86 x y) = (term86 x y).
Proof. exact (eq_refl (term86 x y)). Qed.
Lemma lem1280436 (x : nadd) (y : nadd) (z : nadd) : (term87 x y z) = (term53 x y z).
Proof. exact (MK_COMB (@lem1280435 x y) (@lem1280434 x y z)). Qed.
Lemma lem1280437 (x : nadd) (y : nadd) : (term88 x y) = (term62 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1280436 x y z)). Qed.
Lemma lem1280438 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1280439 (x : nadd) (y : nadd) : (term81 x y) = (term63 x y).
Proof. exact (MK_COMB (@lem1280438) (@lem1280437 x y)). Qed.
Lemma lem1280440 (x : nadd) (y : nadd) : ((term82 x y) = (term81 x y)) = ((term94 x y) = (term63 x y)).
Proof. exact (MK_COMB (@lem1280433 x y) (@lem1280439 x y)). Qed.
Lemma lem1280441 (x : nadd) (y : nadd) : (term94 x y) = (term63 x y).
Proof. exact (EQ_MP (@lem1280440 x y) (@lem1280425 x y)). Qed.
Lemma lem1280442 (x : nadd) : (term95 x) = (term69 x).
Proof. exact (fun_ext (fun y : nadd => @lem1280441 x y)). Qed.
Lemma lem1280443 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1280444 (x : nadd) : (term96 x) = (term70 x).
Proof. exact (MK_COMB (@lem1280443) (@lem1280442 x)). Qed.
Lemma lem1280445 : term97 = term75.
Proof. exact (fun_ext (fun x : nadd => @lem1280444 x)). Qed.
Lemma lem1280446 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1280447 : term98 = term76.
Proof. exact (MK_COMB (@lem1280446) (@lem1280445)). Qed.
Lemma lem1280448 : term76 = term76.
Proof. exact (TRANS (@lem1280417) (@lem1280447)). Qed.
Lemma lem1280449 : term10 = term76.
Proof. exact (TRANS (@lem1280331) (@lem1280448)). Qed.
Lemma lem1280450 (h1 : term10) : term76.
Proof. exact (EQ_MP (@lem1280449) (@lem1280291 h1)). Qed.
Lemma lem1280451 (y : nadd) (x : nadd) : (term41 y x) = (term41 y x).
Proof. exact (eq_refl (term41 y x)). Qed.
Lemma lem1280452 (x : nadd) : (term42 x) = (term42 x).
Proof. exact (fun_ext (fun y : nadd => @lem1280451 y x)). Qed.
Lemma lem1280453 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280454 (x : nadd) : (term43 x) = (term43 x).
Proof. exact (MK_COMB (@lem1280453) (@lem1280452 x)). Qed.
Lemma lem1280455 : term44 = term44.
Proof. exact (fun_ext (fun x : nadd => @lem1280454 x)). Qed.
Lemma lem1280456 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280469 : term45 = term45.
Proof. exact (MK_COMB (@lem1280456) (@lem1280455)). Qed.
Lemma lem1280470 (h1 : term45) : term45.
Proof. exact (EQ_MP (@lem1280469) (@lem1280292 h1)). Qed.
Lemma lem1280477 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term101 x x' y y') = (term102 x x' y y').
Proof. exact (@lem17045 (nadd_eq x x') (nadd_eq y y')). Qed.
Lemma lem1280492 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : ((nadd_le x y) = (nadd_le x' y')) = (term103 x y x' y').
Proof. exact (@lem17784 (nadd_le x y) (nadd_le x' y')). Qed.
Lemma lem1280493 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1280494 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term104 x x' y y') = (term105 x x' y y').
Proof. exact (MK_COMB (@lem1280493) (@lem1280477 x x' y y')). Qed.
Lemma lem1280495 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term106 x y x' y') = (term107 x y x' y').
Proof. exact (MK_COMB (@lem1280494 x x' y y') (@lem1280492 x y x' y')). Qed.
Lemma lem1280496 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term32 x y x' y') = (term106 x y x' y').
Proof. exact (@lem17265 (term108 x x' y y') ((nadd_le x y) = (nadd_le x' y'))). Qed.
Lemma lem1280497 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term32 x y x' y') = (term107 x y x' y').
Proof. exact (TRANS (@lem1280496 x y x' y') (@lem1280495 x y x' y')). Qed.
Lemma lem1280498 (x : nadd) (y : nadd) (x' : nadd) : (term33 x y x') = (term109 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1280497 x y x' y')). Qed.
Lemma lem1280499 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280500 (x : nadd) (y : nadd) (x' : nadd) : (term34 x y x') = (term110 x y x').
Proof. exact (MK_COMB (@lem1280499) (@lem1280498 x y x')). Qed.
Lemma lem1280501 (x : nadd) (x' : nadd) : (term35 x x') = (term111 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1280500 x y x')). Qed.
Lemma lem1280502 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280503 (x : nadd) (x' : nadd) : (term36 x x') = (term112 x x').
Proof. exact (MK_COMB (@lem1280502) (@lem1280501 x x')). Qed.
Lemma lem1280504 (x : nadd) : (term37 x) = (term113 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1280503 x x')). Qed.
Lemma lem1280505 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280506 (x : nadd) : (term38 x) = (term114 x).
Proof. exact (MK_COMB (@lem1280505) (@lem1280504 x)). Qed.
Lemma lem1280507 : term39 = term115.
Proof. exact (fun_ext (fun x : nadd => @lem1280506 x)). Qed.
Lemma lem1280508 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280573 : term40 = term116.
Proof. exact (MK_COMB (@lem1280508) (@lem1280507)). Qed.
Lemma lem1280574 (h1 : term40) : term116.
Proof. exact (EQ_MP (@lem1280573) (@lem1280293 h1)). Qed.
Lemma lem1280581 (y : nadd) (x : nadd) (z : nadd) : (term26 y x z) = (term117 y x z).
Proof. exact (@lem17265 (nadd_le y z) (term118 y x z)). Qed.
Lemma lem1280582 (y : nadd) (x : nadd) : (term27 y x) = (term119 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1280581 y x z)). Qed.
Lemma lem1280583 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280584 (y : nadd) (x : nadd) : (term28 y x) = (term120 y x).
Proof. exact (MK_COMB (@lem1280583) (@lem1280582 y x)). Qed.
Lemma lem1280585 (x : nadd) : (term29 x) = (term121 x).
Proof. exact (fun_ext (fun y : nadd => @lem1280584 y x)). Qed.
Lemma lem1280586 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280587 (x : nadd) : (term30 x) = (term122 x).
Proof. exact (MK_COMB (@lem1280586) (@lem1280585 x)). Qed.
Lemma lem1280588 : term31 = term123.
Proof. exact (fun_ext (fun x : nadd => @lem1280587 x)). Qed.
Lemma lem1280589 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280650 : term17 = term124.
Proof. exact (MK_COMB (@lem1280589) (@lem1280588)). Qed.
Lemma lem1280651 (h1 : term17) : term124.
Proof. exact (EQ_MP (@lem1280650) (@lem1280294 h1)). Qed.
Lemma lem1280652 (x : nadd) (h1 : term70 x) : term70 x.
Proof. exact (h1). Qed.
Lemma lem1280653 (x : nadd) (y : nadd) (h1 : term63 x y) : term63 x y.
Proof. exact (h1). Qed.
Lemma lem1280667 (y : nadd) (x : nadd) : (term41 y x) = (term41 y x).
Proof. exact (eq_refl (term41 y x)). Qed.
Lemma lem1280668 (x : nadd) : (term42 x) = (term42 x).
Proof. exact (fun_ext (fun y : nadd => @lem1280667 y x)). Qed.
Lemma lem1280669 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280670 (x : nadd) : (term43 x) = (term43 x).
Proof. exact (MK_COMB (@lem1280669) (@lem1280668 x)). Qed.
Lemma lem1280671 : term44 = term44.
Proof. exact (fun_ext (fun x : nadd => @lem1280670 x)). Qed.
Lemma lem1280672 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280673 : term45 = term45.
Proof. exact (MK_COMB (@lem1280672) (@lem1280671)). Qed.
Lemma lem1280674 (h1 : term45) : term45.
Proof. exact (EQ_MP (@lem1280673) (@lem1280470 h1)). Qed.
Lemma lem1280727 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term107 x y x' y') = (term107 x y x' y').
Proof. exact (eq_refl (term107 x y x' y')). Qed.
Lemma lem1280728 (x : nadd) (y : nadd) (x' : nadd) : (term109 x y x') = (term109 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1280727 x y x' y')). Qed.
Lemma lem1280729 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280730 (x : nadd) (y : nadd) (x' : nadd) : (term110 x y x') = (term110 x y x').
Proof. exact (MK_COMB (@lem1280729) (@lem1280728 x y x')). Qed.
Lemma lem1280731 (x : nadd) (x' : nadd) : (term111 x x') = (term111 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1280730 x y x')). Qed.
Lemma lem1280732 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280733 (x : nadd) (x' : nadd) : (term112 x x') = (term112 x x').
Proof. exact (MK_COMB (@lem1280732) (@lem1280731 x x')). Qed.
Lemma lem1280734 (x : nadd) : (term113 x) = (term113 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1280733 x x')). Qed.
Lemma lem1280735 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280736 (x : nadd) : (term114 x) = (term114 x).
Proof. exact (MK_COMB (@lem1280735) (@lem1280734 x)). Qed.
Lemma lem1280737 : term115 = term115.
Proof. exact (fun_ext (fun x : nadd => @lem1280736 x)). Qed.
Lemma lem1280738 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280739 : term116 = term116.
Proof. exact (MK_COMB (@lem1280738) (@lem1280737)). Qed.
Lemma lem1280740 (h1 : term40) : term116.
Proof. exact (EQ_MP (@lem1280739) (@lem1280574 h1)). Qed.
Lemma lem1280763 (y : nadd) (x : nadd) (z : nadd) : (term117 y x z) = (term117 y x z).
Proof. exact (eq_refl (term117 y x z)). Qed.
Lemma lem1280764 (y : nadd) (x : nadd) : (term119 y x) = (term119 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1280763 y x z)). Qed.
Lemma lem1280765 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280766 (y : nadd) (x : nadd) : (term120 y x) = (term120 y x).
Proof. exact (MK_COMB (@lem1280765) (@lem1280764 y x)). Qed.
Lemma lem1280767 (x : nadd) : (term121 x) = (term121 x).
Proof. exact (fun_ext (fun y : nadd => @lem1280766 y x)). Qed.
Lemma lem1280768 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280769 (x : nadd) : (term122 x) = (term122 x).
Proof. exact (MK_COMB (@lem1280768) (@lem1280767 x)). Qed.
Lemma lem1280770 : term123 = term123.
Proof. exact (fun_ext (fun x : nadd => @lem1280769 x)). Qed.
Lemma lem1280771 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280772 : term124 = term124.
Proof. exact (MK_COMB (@lem1280771) (@lem1280770)). Qed.
Lemma lem1280773 (h1 : term17) : term124.
Proof. exact (EQ_MP (@lem1280772) (@lem1280651 h1)). Qed.
Lemma lem1280797 (x : nadd) (y : nadd) (z : nadd) (h1 : term53 x y z) : term53 x y z.
Proof. exact (h1). Qed.
Lemma lem1280801 (y : nadd) (x : nadd) : (term41 y x) = (term41 y x).
Proof. exact (eq_refl (term41 y x)). Qed.
Lemma lem1280802 (x : nadd) : (term42 x) = (term42 x).
Proof. exact (fun_ext (fun y : nadd => @lem1280801 y x)). Qed.
Lemma lem1280803 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280804 (x : nadd) : (term43 x) = (term43 x).
Proof. exact (MK_COMB (@lem1280803) (@lem1280802 x)). Qed.
Lemma lem1280805 : term44 = term44.
Proof. exact (fun_ext (fun x : nadd => @lem1280804 x)). Qed.
Lemma lem1280806 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280808 : term45 = term45.
Proof. exact (MK_COMB (@lem1280806) (@lem1280805)). Qed.
Lemma lem1280809 (h1 : term45) : term45.
Proof. exact (EQ_MP (@lem1280808) (@lem1280674 h1)). Qed.
Lemma lem1280845 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term107 x y x' y') = (term125 x y x' y').
Proof. exact (@lem19490 (term126 x y x' y') (term102 x x' y y') (term127 x y x' y')). Qed.
Lemma lem1280846 (x : nadd) (y : nadd) (x' : nadd) : (term109 x y x') = (term128 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1280845 x y x' y')). Qed.
Lemma lem1280847 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280848 (x : nadd) (y : nadd) (x' : nadd) : (term110 x y x') = (term129 x y x').
Proof. exact (MK_COMB (@lem1280847) (@lem1280846 x y x')). Qed.
Lemma lem1280849 (x : nadd) (x' : nadd) : (term111 x x') = (term130 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1280848 x y x')). Qed.
Lemma lem1280850 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280851 (x : nadd) (x' : nadd) : (term112 x x') = (term131 x x').
Proof. exact (MK_COMB (@lem1280850) (@lem1280849 x x')). Qed.
Lemma lem1280852 (x : nadd) : (term113 x) = (term132 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1280851 x x')). Qed.
Lemma lem1280853 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280854 (x : nadd) : (term114 x) = (term133 x).
Proof. exact (MK_COMB (@lem1280853) (@lem1280852 x)). Qed.
Lemma lem1280855 : term115 = term134.
Proof. exact (fun_ext (fun x : nadd => @lem1280854 x)). Qed.
Lemma lem1280856 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280858 : term116 = term135.
Proof. exact (MK_COMB (@lem1280856) (@lem1280855)). Qed.
Lemma lem1280859 (h1 : term40) : term135.
Proof. exact (EQ_MP (@lem1280858) (@lem1280740 h1)). Qed.
Lemma lem1280867 (y : nadd) (x : nadd) (z : nadd) : (term117 y x z) = (term117 y x z).
Proof. exact (eq_refl (term117 y x z)). Qed.
Lemma lem1280868 (y : nadd) (x : nadd) : (term119 y x) = (term119 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1280867 y x z)). Qed.
Lemma lem1280869 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280870 (y : nadd) (x : nadd) : (term120 y x) = (term120 y x).
Proof. exact (MK_COMB (@lem1280869) (@lem1280868 y x)). Qed.
Lemma lem1280871 (x : nadd) : (term121 x) = (term121 x).
Proof. exact (fun_ext (fun y : nadd => @lem1280870 y x)). Qed.
Lemma lem1280872 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280873 (x : nadd) : (term122 x) = (term122 x).
Proof. exact (MK_COMB (@lem1280872) (@lem1280871 x)). Qed.
Lemma lem1280874 : term123 = term123.
Proof. exact (fun_ext (fun x : nadd => @lem1280873 x)). Qed.
Lemma lem1280875 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1280877 : term124 = term124.
Proof. exact (MK_COMB (@lem1280875) (@lem1280874)). Qed.
Lemma lem1280878 (h1 : term17) : term124.
Proof. exact (EQ_MP (@lem1280877) (@lem1280773 h1)). Qed.
Lemma lem1280887 (_23210 : nadd) (h1 : term45) : term136 _23210.
Proof. exact (@lem1280809 h1 _23210). Qed.
Lemma lem1280888 (_23210 : nadd) : (term136 _23210) = (term43 _23210).
Proof. exact (eq_refl (term136 _23210)). Qed.
Lemma lem1280889 (_23210 : nadd) (h1 : term45) : term43 _23210.
Proof. exact (EQ_MP (@lem1280888 _23210) (@lem1280887 _23210 h1)). Qed.
Lemma lem1280890 (_23210 : nadd) (_23211 : nadd) (h1 : term45) : term137 _23210 _23211.
Proof. exact (@lem1280889 _23210 h1 _23211). Qed.
Lemma lem1280891 (_23211 : nadd) (_23210 : nadd) : (term137 _23210 _23211) = (term41 _23211 _23210).
Proof. exact (eq_refl (term137 _23210 _23211)). Qed.
Lemma lem1280893 (_23212 : nadd) (h1 : term40) : term138 _23212.
Proof. exact (@lem1280859 h1 _23212). Qed.
Lemma lem1280894 (_23212 : nadd) : (term138 _23212) = (term133 _23212).
Proof. exact (eq_refl (term138 _23212)). Qed.
Lemma lem1280895 (_23212 : nadd) (h1 : term40) : term133 _23212.
Proof. exact (EQ_MP (@lem1280894 _23212) (@lem1280893 _23212 h1)). Qed.
Lemma lem1280896 (_23212 : nadd) (_23213 : nadd) (h1 : term40) : term139 _23212 _23213.
Proof. exact (@lem1280895 _23212 h1 _23213). Qed.
Lemma lem1280897 (_23212 : nadd) (_23213 : nadd) : (term139 _23212 _23213) = (term131 _23212 _23213).
Proof. exact (eq_refl (term139 _23212 _23213)). Qed.
Lemma lem1280898 (_23212 : nadd) (_23213 : nadd) (h1 : term40) : term131 _23212 _23213.
Proof. exact (EQ_MP (@lem1280897 _23212 _23213) (@lem1280896 _23212 _23213 h1)). Qed.
Lemma lem1280899 (_23212 : nadd) (_23213 : nadd) (_23214 : nadd) (h1 : term40) : term140 _23212 _23213 _23214.
Proof. exact (@lem1280898 _23212 _23213 h1 _23214). Qed.
Lemma lem1280900 (_23212 : nadd) (_23214 : nadd) (_23213 : nadd) : (term140 _23212 _23213 _23214) = (term129 _23212 _23214 _23213).
Proof. exact (eq_refl (term140 _23212 _23213 _23214)). Qed.
Lemma lem1280901 (_23212 : nadd) (_23214 : nadd) (_23213 : nadd) (h1 : term40) : term129 _23212 _23214 _23213.
Proof. exact (EQ_MP (@lem1280900 _23212 _23214 _23213) (@lem1280899 _23212 _23213 _23214 h1)). Qed.
Lemma lem1280902 (_23212 : nadd) (_23214 : nadd) (_23213 : nadd) (_23215 : nadd) (h1 : term40) : term141 _23212 _23214 _23213 _23215.
Proof. exact (@lem1280901 _23212 _23214 _23213 h1 _23215). Qed.
Lemma lem1280903 (_23212 : nadd) (_23214 : nadd) (_23213 : nadd) (_23215 : nadd) : (term141 _23212 _23214 _23213 _23215) = (term125 _23212 _23214 _23213 _23215).
Proof. exact (eq_refl (term141 _23212 _23214 _23213 _23215)). Qed.
Lemma lem1280904 (_23212 : nadd) (_23214 : nadd) (_23213 : nadd) (_23215 : nadd) (h1 : term40) : term125 _23212 _23214 _23213 _23215.
Proof. exact (EQ_MP (@lem1280903 _23212 _23214 _23213 _23215) (@lem1280902 _23212 _23214 _23213 _23215 h1)). Qed.
Lemma lem1280905 (_23216 : nadd) (h1 : term17) : term142 _23216.
Proof. exact (@lem1280878 h1 _23216). Qed.
Lemma lem1280906 (_23216 : nadd) : (term142 _23216) = (term122 _23216).
Proof. exact (eq_refl (term142 _23216)). Qed.
Lemma lem1280907 (_23216 : nadd) (h1 : term17) : term122 _23216.
Proof. exact (EQ_MP (@lem1280906 _23216) (@lem1280905 _23216 h1)). Qed.
Lemma lem1280908 (_23216 : nadd) (_23217 : nadd) (h1 : term17) : term143 _23216 _23217.
Proof. exact (@lem1280907 _23216 h1 _23217). Qed.
Lemma lem1280909 (_23217 : nadd) (_23216 : nadd) : (term143 _23216 _23217) = (term120 _23217 _23216).
Proof. exact (eq_refl (term143 _23216 _23217)). Qed.
Lemma lem1280910 (_23217 : nadd) (_23216 : nadd) (h1 : term17) : term120 _23217 _23216.
Proof. exact (EQ_MP (@lem1280909 _23217 _23216) (@lem1280908 _23216 _23217 h1)). Qed.
Lemma lem1280911 (_23217 : nadd) (_23216 : nadd) (_23218 : nadd) (h1 : term17) : term144 _23217 _23216 _23218.
Proof. exact (@lem1280910 _23217 _23216 h1 _23218). Qed.
Lemma lem1280912 (_23217 : nadd) (_23216 : nadd) (_23218 : nadd) : (term144 _23217 _23216 _23218) = (term117 _23217 _23216 _23218).
Proof. exact (eq_refl (term144 _23217 _23216 _23218)). Qed.
Lemma lem1280914 (_23212 : nadd) (_23214 : nadd) (_23213 : nadd) (_23215 : nadd) (h1 : term40) : term145 _23212 _23214 _23213 _23215.
Proof. exact (proj2 (@lem1280904 _23212 _23214 _23213 _23215 h1)). Qed.
Lemma lem1280923 (_23217 : nadd) (_23216 : nadd) (_23218 : nadd) (h1 : term17) : term117 _23217 _23216 _23218.
Proof. exact (EQ_MP (@lem1280912 _23217 _23216 _23218) (@lem1280911 _23217 _23216 _23218 h1)). Qed.
Lemma lem1280927 (x : nadd) (y : nadd) (z : nadd) (h1 : term53 x y z) : term85 x y z.
Proof. exact (proj2 (@lem1280797 x y z h1)). Qed.
Lemma lem1280958 (_23212 : nadd) (_23214 : nadd) (_23213 : nadd) (_23215 : nadd) : (term145 _23212 _23214 _23213 _23215) = (term146 _23212 _23214 _23213 _23215).
Proof. exact (@lem1280026 (term147 _23212 _23213) (term147 _23214 _23215) (term127 _23212 _23214 _23213 _23215)). Qed.
Lemma lem1280959 (_23212 : nadd) (_23214 : nadd) (_23213 : nadd) (_23215 : nadd) (h1 : term40) : term146 _23212 _23214 _23213 _23215.
Proof. exact (EQ_MP (@lem1280958 _23212 _23214 _23213 _23215) (@lem1280914 _23212 _23214 _23213 _23215 h1)). Qed.
Lemma lem1280961 (_23211 : nadd) (_23210 : nadd) (h1 : term45) : term41 _23211 _23210.
Proof. exact (EQ_MP (@lem1280891 _23211 _23210) (@lem1280890 _23210 _23211 h1)). Qed.
Lemma lem1280962 (x : nadd) (z : nadd) (h1 : term45) : term41 x z.
Proof. exact (@lem1280961 x z h1). Qed.
Lemma lem1280963 (x : nadd) (z : nadd) (h1 : term45) : term148 x z.
Proof. exact (fun h0 : term149 x z => @lem1280962 x z h1). Qed.
Lemma lem1280965 (p : Prop) : (term150 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1280966 (x : nadd) (z : nadd) : (term148 x z) = (term41 x z).
Proof. exact (@lem1280965 (term41 x z)). Qed.
Lemma lem1280967 (x : nadd) (z : nadd) (h1 : term45) : term41 x z.
Proof. exact (EQ_MP (@lem1280966 x z) (@lem1280963 x z h1)). Qed.
Lemma lem1280969 (_23211 : nadd) (_23210 : nadd) (h1 : term45) : term41 _23211 _23210.
Proof. exact (EQ_MP (@lem1280891 _23211 _23210) (@lem1280890 _23210 _23211 h1)). Qed.
Lemma lem1280970 (y : nadd) (z : nadd) (h1 : term45) : term41 y z.
Proof. exact (@lem1280969 y z h1). Qed.
Lemma lem1280971 (y : nadd) (z : nadd) (h1 : term45) : term148 y z.
Proof. exact (fun h0 : term149 y z => @lem1280970 y z h1). Qed.
Lemma lem1280973 (p : Prop) : (term150 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1280974 (y : nadd) (z : nadd) : (term148 y z) = (term41 y z).
Proof. exact (@lem1280973 (term41 y z)). Qed.
Lemma lem1280975 (y : nadd) (z : nadd) (h1 : term45) : term41 y z.
Proof. exact (EQ_MP (@lem1280974 y z) (@lem1280971 y z h1)). Qed.
Lemma lem1280977 (x : nadd) (y : nadd) (z : nadd) (h1 : term53 x y z) : nadd_le x y.
Proof. exact (proj1 (@lem1280797 x y z h1)). Qed.
Lemma lem1280978 (x : nadd) (y : nadd) (z : nadd) (h1 : term53 x y z) : term151 x y.
Proof. exact (fun h0 : term152 x y => @lem1280977 x y z h1). Qed.
Lemma lem1280980 (p : Prop) : (term150 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1280981 (x : nadd) (y : nadd) : (term151 x y) = (nadd_le x y).
Proof. exact (@lem1280980 (nadd_le x y)). Qed.
Lemma lem1280982 (x : nadd) (y : nadd) (z : nadd) (h1 : term53 x y z) : nadd_le x y.
Proof. exact (EQ_MP (@lem1280981 x y) (@lem1280978 x y z h1)). Qed.
Lemma lem1280988 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1280989 (_23216 : nadd) (_23217 : nadd) (_23218 : nadd) : (term117 _23217 _23216 _23218) = (term153 _23216 _23217 _23218).
Proof. exact (@lem1280988 (term118 _23217 _23216 _23218) (term152 _23217 _23218)). Qed.
Lemma lem1280995 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1280996 (_23216 : nadd) (_23217 : nadd) (_23218 : nadd) : (term154 _23217 _23216 _23218) = (term155 _23216 _23217 _23218).
Proof. exact (MK_COMB (@lem1280995) (@lem1280989 _23216 _23217 _23218)). Qed.
Lemma lem1281002 (_23216 : nadd) (_23217 : nadd) (_23218 : nadd) : (term153 _23216 _23217 _23218) = (term153 _23216 _23217 _23218).
Proof. exact (eq_refl (term153 _23216 _23217 _23218)). Qed.
Lemma lem1281003 (_23216 : nadd) (_23217 : nadd) (_23218 : nadd) : ((term117 _23217 _23216 _23218) = (term153 _23216 _23217 _23218)) = ((term153 _23216 _23217 _23218) = (term153 _23216 _23217 _23218)).
Proof. exact (MK_COMB (@lem1280996 _23216 _23217 _23218) (@lem1281002 _23216 _23217 _23218)). Qed.
Lemma lem1281005 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1281006 (x : Prop) : (x = x) = True.
Proof. exact (@lem1281005 Prop x). Qed.
Lemma lem1281007 (_23216 : nadd) (_23217 : nadd) (_23218 : nadd) : ((term153 _23216 _23217 _23218) = (term153 _23216 _23217 _23218)) = True.
Proof. exact (@lem1281006 (term153 _23216 _23217 _23218)). Qed.
Lemma lem1281008 (_23216 : nadd) (_23217 : nadd) (_23218 : nadd) : ((term117 _23217 _23216 _23218) = (term153 _23216 _23217 _23218)) = True.
Proof. exact (TRANS (@lem1281003 _23216 _23217 _23218) (@lem1281007 _23216 _23217 _23218)). Qed.
Lemma lem1281009 (_23216 : nadd) (_23217 : nadd) (_23218 : nadd) : True = ((term117 _23217 _23216 _23218) = (term153 _23216 _23217 _23218)).
Proof. exact (SYM (@lem1281008 _23216 _23217 _23218)). Qed.
Lemma lem1281010 (_23216 : nadd) (_23217 : nadd) (_23218 : nadd) : (term117 _23217 _23216 _23218) = (term153 _23216 _23217 _23218).
Proof. exact (EQ_MP (@lem1281009 _23216 _23217 _23218) (@lem0)). Qed.
Lemma lem1281011 (_23216 : nadd) (_23217 : nadd) (_23218 : nadd) (h1 : term17) : term153 _23216 _23217 _23218.
Proof. exact (EQ_MP (@lem1281010 _23216 _23217 _23218) (@lem1280923 _23217 _23216 _23218 h1)). Qed.
Lemma lem1281013 (b : Prop) (a : Prop) : (a \/ b) = (term156 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1281014 (_23217 : nadd) (_23216 : nadd) (_23218 : nadd) : (term153 _23216 _23217 _23218) = (term157 _23217 _23216 _23218).
Proof. exact (@lem1281013 (term152 _23217 _23218) (term118 _23217 _23216 _23218)). Qed.
Lemma lem1281016 (a : Prop) : (term158 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1281017 (_23217 : nadd) (_23218 : nadd) : (term159 _23217 _23218) = (nadd_le _23217 _23218).
Proof. exact (@lem1281016 (nadd_le _23217 _23218)). Qed.
Lemma lem1281018 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1281019 (_23217 : nadd) (_23218 : nadd) : (term160 _23217 _23218) = (term161 _23217 _23218).
Proof. exact (MK_COMB (@lem1281018) (@lem1281017 _23217 _23218)). Qed.
Lemma lem1281020 (_23217 : nadd) (_23216 : nadd) (_23218 : nadd) : (term118 _23217 _23216 _23218) = (term118 _23217 _23216 _23218).
Proof. exact (eq_refl (term118 _23217 _23216 _23218)). Qed.
Lemma lem1281021 (_23217 : nadd) (_23216 : nadd) (_23218 : nadd) : (term157 _23217 _23216 _23218) = (term26 _23217 _23216 _23218).
Proof. exact (MK_COMB (@lem1281019 _23217 _23218) (@lem1281020 _23217 _23216 _23218)). Qed.
Lemma lem1281022 (_23217 : nadd) (_23216 : nadd) (_23218 : nadd) : (term153 _23216 _23217 _23218) = (term26 _23217 _23216 _23218).
Proof. exact (TRANS (@lem1281014 _23217 _23216 _23218) (@lem1281021 _23217 _23216 _23218)). Qed.
Lemma lem1281025 (_23217 : nadd) (_23216 : nadd) (_23218 : nadd) (h1 : term17) : term26 _23217 _23216 _23218.
Proof. exact (EQ_MP (@lem1281022 _23217 _23216 _23218) (@lem1281011 _23216 _23217 _23218 h1)). Qed.
Lemma lem1281026 (x : nadd) (_23216 : nadd) (y : nadd) (h1 : term17) : term26 x _23216 y.
Proof. exact (@lem1281025 x _23216 y h1). Qed.
Lemma lem1281029 (_23216 : nadd) (x : nadd) (y : nadd) (z : nadd) (h1 : term17) (h2 : term53 x y z) : term118 x _23216 y.
Proof. exact (@lem1281026 x _23216 y h1 (@lem1280982 x y z h2)). Qed.
Lemma lem1281030 (x : nadd) (y : nadd) (z : nadd) (h1 : term17) (h2 : term53 x y z) : term118 x z y.
Proof. exact (@lem1281029 z x y z h1 h2). Qed.
Lemma lem1281031 (x : nadd) (y : nadd) (z : nadd) (h1 : term17) (h2 : term53 x y z) : term162 x z y.
Proof. exact (fun h0 : term163 x z y => @lem1281030 x y z h1 h2). Qed.
Lemma lem1281033 (p : Prop) : (term150 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1281034 (x : nadd) (z : nadd) (y : nadd) : (term162 x z y) = (term118 x z y).
Proof. exact (@lem1281033 (term118 x z y)). Qed.
Lemma lem1281035 (x : nadd) (y : nadd) (z : nadd) (h1 : term17) (h2 : term53 x y z) : term118 x z y.
Proof. exact (EQ_MP (@lem1281034 x z y) (@lem1281031 x y z h1 h2)). Qed.
Lemma lem1281061 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1281062 (_23213 : nadd) (_23215 : nadd) (_23212 : nadd) (_23214 : nadd) : (term127 _23212 _23214 _23213 _23215) = (term126 _23213 _23215 _23212 _23214).
Proof. exact (@lem1281061 (nadd_le _23213 _23215) (term152 _23212 _23214)). Qed.
Lemma lem1281068 (_23214 : nadd) (_23215 : nadd) : (term164 _23214 _23215) = (term164 _23214 _23215).
Proof. exact (eq_refl (term164 _23214 _23215)). Qed.
Lemma lem1281069 (_23213 : nadd) (_23215 : nadd) (_23212 : nadd) (_23214 : nadd) : (term165 _23212 _23214 _23213 _23215) = (term166 _23213 _23215 _23212 _23214).
Proof. exact (MK_COMB (@lem1281068 _23214 _23215) (@lem1281062 _23213 _23215 _23212 _23214)). Qed.
Lemma lem1281073 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1281074 (_23213 : nadd) (_23215 : nadd) (_23212 : nadd) (_23214 : nadd) : (term166 _23213 _23215 _23212 _23214) = (term167 _23213 _23215 _23212 _23214).
Proof. exact (@lem1281073 (nadd_le _23213 _23215) (term147 _23214 _23215) (term152 _23212 _23214)). Qed.
Lemma lem1281090 (_23213 : nadd) (_23215 : nadd) (_23212 : nadd) (_23214 : nadd) : (term165 _23212 _23214 _23213 _23215) = (term167 _23213 _23215 _23212 _23214).
Proof. exact (TRANS (@lem1281069 _23213 _23215 _23212 _23214) (@lem1281074 _23213 _23215 _23212 _23214)). Qed.
Lemma lem1281091 (_23212 : nadd) (_23213 : nadd) : (term164 _23212 _23213) = (term164 _23212 _23213).
Proof. exact (eq_refl (term164 _23212 _23213)). Qed.
Lemma lem1281092 (_23213 : nadd) (_23215 : nadd) (_23212 : nadd) (_23214 : nadd) : (term146 _23212 _23214 _23213 _23215) = (term168 _23213 _23215 _23212 _23214).
Proof. exact (MK_COMB (@lem1281091 _23212 _23213) (@lem1281090 _23213 _23215 _23212 _23214)). Qed.
Lemma lem1281096 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1281097 (_23213 : nadd) (_23215 : nadd) (_23212 : nadd) (_23214 : nadd) : (term168 _23213 _23215 _23212 _23214) = (term169 _23213 _23215 _23212 _23214).
Proof. exact (@lem1281096 (nadd_le _23213 _23215) (term147 _23212 _23213) (term170 _23215 _23212 _23214)). Qed.
Lemma lem1281123 (_23213 : nadd) (_23215 : nadd) (_23212 : nadd) (_23214 : nadd) : (term146 _23212 _23214 _23213 _23215) = (term169 _23213 _23215 _23212 _23214).
Proof. exact (TRANS (@lem1281092 _23213 _23215 _23212 _23214) (@lem1281097 _23213 _23215 _23212 _23214)). Qed.
Lemma lem1281124 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1281125 (_23213 : nadd) (_23215 : nadd) (_23212 : nadd) (_23214 : nadd) : (term171 _23212 _23214 _23213 _23215) = (term172 _23213 _23215 _23212 _23214).
Proof. exact (MK_COMB (@lem1281124) (@lem1281123 _23213 _23215 _23212 _23214)). Qed.
Lemma lem1281151 (_23213 : nadd) (_23215 : nadd) (_23212 : nadd) (_23214 : nadd) : (term169 _23213 _23215 _23212 _23214) = (term169 _23213 _23215 _23212 _23214).
Proof. exact (eq_refl (term169 _23213 _23215 _23212 _23214)). Qed.
Lemma lem1281152 (_23213 : nadd) (_23215 : nadd) (_23212 : nadd) (_23214 : nadd) : ((term146 _23212 _23214 _23213 _23215) = (term169 _23213 _23215 _23212 _23214)) = ((term169 _23213 _23215 _23212 _23214) = (term169 _23213 _23215 _23212 _23214)).
Proof. exact (MK_COMB (@lem1281125 _23213 _23215 _23212 _23214) (@lem1281151 _23213 _23215 _23212 _23214)). Qed.
Lemma lem1281154 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1281155 (x : Prop) : (x = x) = True.
Proof. exact (@lem1281154 Prop x). Qed.
Lemma lem1281156 (_23213 : nadd) (_23215 : nadd) (_23212 : nadd) (_23214 : nadd) : ((term169 _23213 _23215 _23212 _23214) = (term169 _23213 _23215 _23212 _23214)) = True.
Proof. exact (@lem1281155 (term169 _23213 _23215 _23212 _23214)). Qed.
Lemma lem1281157 (_23213 : nadd) (_23215 : nadd) (_23212 : nadd) (_23214 : nadd) : ((term146 _23212 _23214 _23213 _23215) = (term169 _23213 _23215 _23212 _23214)) = True.
Proof. exact (TRANS (@lem1281152 _23213 _23215 _23212 _23214) (@lem1281156 _23213 _23215 _23212 _23214)). Qed.
Lemma lem1281158 (_23213 : nadd) (_23215 : nadd) (_23212 : nadd) (_23214 : nadd) : True = ((term146 _23212 _23214 _23213 _23215) = (term169 _23213 _23215 _23212 _23214)).
Proof. exact (SYM (@lem1281157 _23213 _23215 _23212 _23214)). Qed.
Lemma lem1281159 (_23213 : nadd) (_23215 : nadd) (_23212 : nadd) (_23214 : nadd) : (term146 _23212 _23214 _23213 _23215) = (term169 _23213 _23215 _23212 _23214).
Proof. exact (EQ_MP (@lem1281158 _23213 _23215 _23212 _23214) (@lem0)). Qed.
Lemma lem1281160 (_23213 : nadd) (_23215 : nadd) (_23212 : nadd) (_23214 : nadd) (h1 : term40) : term169 _23213 _23215 _23212 _23214.
Proof. exact (EQ_MP (@lem1281159 _23213 _23215 _23212 _23214) (@lem1280959 _23212 _23214 _23213 _23215 h1)). Qed.
Lemma lem1281162 (b : Prop) (a : Prop) : (a \/ b) = (term156 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1281163 (_23212 : nadd) (_23214 : nadd) (_23213 : nadd) (_23215 : nadd) : (term169 _23213 _23215 _23212 _23214) = (term173 _23212 _23214 _23213 _23215).
Proof. exact (@lem1281162 (term174 _23213 _23215 _23212 _23214) (nadd_le _23213 _23215)). Qed.
Lemma lem1281165 (a : Prop) (b : Prop) : (term175 a b) = (term176 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1281166 (_23213 : nadd) (_23215 : nadd) (_23212 : nadd) (_23214 : nadd) : (term177 _23213 _23215 _23212 _23214) = (term178 _23213 _23215 _23212 _23214).
Proof. exact (@lem1281165 (term147 _23212 _23213) (term170 _23215 _23212 _23214)). Qed.
Lemma lem1281168 (a : Prop) : (term158 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1281169 (_23212 : nadd) (_23213 : nadd) : (term179 _23212 _23213) = (nadd_eq _23212 _23213).
Proof. exact (@lem1281168 (nadd_eq _23212 _23213)). Qed.
Lemma lem1281170 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1281171 (_23212 : nadd) (_23213 : nadd) : (term180 _23212 _23213) = (term181 _23212 _23213).
Proof. exact (MK_COMB (@lem1281170) (@lem1281169 _23212 _23213)). Qed.
Lemma lem1281173 (a : Prop) (b : Prop) : (term175 a b) = (term176 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1281174 (_23215 : nadd) (_23212 : nadd) (_23214 : nadd) : (term182 _23215 _23212 _23214) = (term183 _23215 _23212 _23214).
Proof. exact (@lem1281173 (term147 _23214 _23215) (term152 _23212 _23214)). Qed.
Lemma lem1281176 (a : Prop) : (term158 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1281177 (_23214 : nadd) (_23215 : nadd) : (term179 _23214 _23215) = (nadd_eq _23214 _23215).
Proof. exact (@lem1281176 (nadd_eq _23214 _23215)). Qed.
Lemma lem1281178 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1281179 (_23214 : nadd) (_23215 : nadd) : (term180 _23214 _23215) = (term181 _23214 _23215).
Proof. exact (MK_COMB (@lem1281178) (@lem1281177 _23214 _23215)). Qed.
Lemma lem1281181 (a : Prop) : (term158 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1281182 (_23212 : nadd) (_23214 : nadd) : (term159 _23212 _23214) = (nadd_le _23212 _23214).
Proof. exact (@lem1281181 (nadd_le _23212 _23214)). Qed.
Lemma lem1281183 (_23215 : nadd) (_23212 : nadd) (_23214 : nadd) : (term183 _23215 _23212 _23214) = (term184 _23215 _23212 _23214).
Proof. exact (MK_COMB (@lem1281179 _23214 _23215) (@lem1281182 _23212 _23214)). Qed.
Lemma lem1281184 (_23215 : nadd) (_23212 : nadd) (_23214 : nadd) : (term182 _23215 _23212 _23214) = (term184 _23215 _23212 _23214).
Proof. exact (TRANS (@lem1281174 _23215 _23212 _23214) (@lem1281183 _23215 _23212 _23214)). Qed.
Lemma lem1281185 (_23213 : nadd) (_23215 : nadd) (_23212 : nadd) (_23214 : nadd) : (term178 _23213 _23215 _23212 _23214) = (term185 _23213 _23215 _23212 _23214).
Proof. exact (MK_COMB (@lem1281171 _23212 _23213) (@lem1281184 _23215 _23212 _23214)). Qed.
Lemma lem1281186 (_23213 : nadd) (_23215 : nadd) (_23212 : nadd) (_23214 : nadd) : (term177 _23213 _23215 _23212 _23214) = (term185 _23213 _23215 _23212 _23214).
Proof. exact (TRANS (@lem1281166 _23213 _23215 _23212 _23214) (@lem1281185 _23213 _23215 _23212 _23214)). Qed.
Lemma lem1281187 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1281188 (_23213 : nadd) (_23215 : nadd) (_23212 : nadd) (_23214 : nadd) : (term186 _23213 _23215 _23212 _23214) = (term187 _23213 _23215 _23212 _23214).
Proof. exact (MK_COMB (@lem1281187) (@lem1281186 _23213 _23215 _23212 _23214)). Qed.
Lemma lem1281189 (_23213 : nadd) (_23215 : nadd) : (nadd_le _23213 _23215) = (nadd_le _23213 _23215).
Proof. exact (eq_refl (nadd_le _23213 _23215)). Qed.
Lemma lem1281190 (_23212 : nadd) (_23214 : nadd) (_23213 : nadd) (_23215 : nadd) : (term173 _23212 _23214 _23213 _23215) = (term188 _23212 _23214 _23213 _23215).
Proof. exact (MK_COMB (@lem1281188 _23213 _23215 _23212 _23214) (@lem1281189 _23213 _23215)). Qed.
Lemma lem1281191 (_23212 : nadd) (_23214 : nadd) (_23213 : nadd) (_23215 : nadd) : (term169 _23213 _23215 _23212 _23214) = (term188 _23212 _23214 _23213 _23215).
Proof. exact (TRANS (@lem1281163 _23212 _23214 _23213 _23215) (@lem1281190 _23212 _23214 _23213 _23215)). Qed.
Lemma lem1281193 (x : nadd) (y : nadd) (z : nadd) (h1 : term17) (h2 : term45) (h3 : term53 x y z) : term189 x z y.
Proof. exact (conj (@lem1280975 y z h2) (@lem1281035 x y z h1 h3)). Qed.
Lemma lem1281194 (x : nadd) (y : nadd) (z : nadd) (h1 : term17) (h2 : term45) (h3 : term53 x y z) : term190 x z y.
Proof. exact (conj (@lem1280967 x z h2) (@lem1281193 x y z h1 h2 h3)). Qed.
Lemma lem1281196 (_23212 : nadd) (_23214 : nadd) (_23213 : nadd) (_23215 : nadd) (h1 : term40) : term188 _23212 _23214 _23213 _23215.
Proof. exact (EQ_MP (@lem1281191 _23212 _23214 _23213 _23215) (@lem1281160 _23213 _23215 _23212 _23214 h1)). Qed.
Lemma lem1281197 (x : nadd) (y : nadd) (z : nadd) (h1 : term40) : term191 x y z.
Proof. exact (@lem1281196 (nadd_mul z x) (nadd_mul z y) (nadd_mul x z) (nadd_mul y z) h1). Qed.
Lemma lem1281200 (x : nadd) (y : nadd) (z : nadd) (h1 : term40) (h2 : term17) (h3 : term45) (h4 : term53 x y z) : term54 x y z.
Proof. exact (@lem1281197 x y z h1 (@lem1281194 x y z h2 h3 h4)). Qed.
Lemma lem1281201 (x : nadd) (y : nadd) (z : nadd) (h1 : term40) (h2 : term17) (h3 : term45) (h4 : term53 x y z) : term192 x y z.
Proof. exact (fun h0 : term85 x y z => @lem1281200 x y z h1 h2 h3 h4). Qed.
Lemma lem1281203 (p : Prop) : (term150 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1281204 (x : nadd) (y : nadd) (z : nadd) : (term192 x y z) = (term54 x y z).
Proof. exact (@lem1281203 (term54 x y z)). Qed.
Lemma lem1281205 (x : nadd) (y : nadd) (z : nadd) (h1 : term40) (h2 : term17) (h3 : term45) (h4 : term53 x y z) : term54 x y z.
Proof. exact (EQ_MP (@lem1281204 x y z) (@lem1281201 x y z h1 h2 h3 h4)). Qed.
Lemma lem1281208 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1281210 (x : nadd) (y : nadd) (z : nadd) : (term85 x y z) = (term193 x y z).
Proof. exact (@lem1281208 (term54 x y z)). Qed.
Lemma lem1281213 (x : nadd) (y : nadd) (z : nadd) (h1 : term53 x y z) : term193 x y z.
Proof. exact (EQ_MP (@lem1281210 x y z) (@lem1280927 x y z h1)). Qed.
Lemma lem1281216 (x : nadd) (y : nadd) (z : nadd) (h1 : term40) (h2 : term17) (h3 : term45) (h4 : term53 x y z) : False.
Proof. exact (@lem1281213 x y z h4 (@lem1281205 x y z h1 h2 h3 h4)). Qed.
Lemma lem1281217 (x : nadd) (y : nadd) (z : nadd) (h1 : term40) (h2 : term17) (h3 : term45) (h4 : term53 x y z) : term194.
Proof. exact (fun h0 : ~ False => @lem1281216 x y z h1 h2 h3 h4). Qed.
Lemma lem1281219 (p : Prop) : (term150 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1281220 : term194 = False.
Proof. exact (@lem1281219 False). Qed.
Lemma lem1281221 (x : nadd) (y : nadd) (z : nadd) (h1 : term40) (h2 : term17) (h3 : term45) (h4 : term53 x y z) : False.
Proof. exact (EQ_MP (@lem1281220) (@lem1281217 x y z h1 h2 h3 h4)). Qed.
Lemma lem1281222 (x : nadd) (y : nadd) (z : nadd) (h1 : term40) (h2 : term17) (h3 : term45) (h4 : term53 x y z) : term45 = False.
Proof. exact (prop_ext (fun h5 : term45 => @lem1281221 x y z h1 h2 h3 h4) (fun h5 : False => @lem1280809 h3)). Qed.
Lemma lem1281223 (x : nadd) (y : nadd) (z : nadd) (h1 : term40) (h2 : term17) (h3 : term45) (h4 : term53 x y z) : False.
Proof. exact (EQ_MP (@lem1281222 x y z h1 h2 h3 h4) (@lem1280809 h3)). Qed.
Lemma lem1281224 (x : nadd) (y : nadd) (z : nadd) (h1 : term40) (h2 : term17) (h3 : term45) (h4 : term53 x y z) : (term53 x y z) = False.
Proof. exact (prop_ext (fun h5 : term53 x y z => @lem1281223 x y z h1 h2 h3 h4) (fun h5 : False => @lem1280797 x y z h4)). Qed.
Lemma lem1281225 (x : nadd) (y : nadd) (z : nadd) (h1 : term40) (h2 : term17) (h3 : term45) (h4 : term53 x y z) : False.
Proof. exact (EQ_MP (@lem1281224 x y z h1 h2 h3 h4) (@lem1280797 x y z h4)). Qed.
Lemma lem1281226 (x : nadd) (y : nadd) (z : nadd) (h1 : term40) (h2 : term17) (h3 : term45) (h4 : term53 x y z) : term45 = False.
Proof. exact (prop_ext (fun h5 : term45 => @lem1281225 x y z h1 h2 h3 h4) (fun h5 : False => @lem1280674 h3)). Qed.
Lemma lem1281227 (x : nadd) (y : nadd) (z : nadd) (h1 : term40) (h2 : term17) (h3 : term45) (h4 : term53 x y z) : False.
Proof. exact (EQ_MP (@lem1281226 x y z h1 h2 h3 h4) (@lem1280674 h3)). Qed.
Lemma lem1281228 (x : nadd) (y : nadd) (h1 : term40) (h2 : term17) (h3 : term45) (h4 : term63 x y) : False.
Proof. exact (ex_elim (@lem1280653 x y h4) (fun z : nadd => fun h0 : term62 x y z => @lem1281227 x y z h1 h2 h3 h0)). Qed.
Lemma lem1281229 (x : nadd) (h1 : term40) (h2 : term17) (h3 : term45) (h4 : term70 x) : False.
Proof. exact (ex_elim (@lem1280652 x h4) (fun y : nadd => fun h0 : term69 x y => @lem1281228 x y h1 h2 h3 h0)). Qed.
Lemma lem1281230 (h1 : term40) (h2 : term17) (h3 : term45) (h4 : term10) : False.
Proof. exact (ex_elim (@lem1280450 h4) (fun x : nadd => fun h0 : term75 x => @lem1281229 x h1 h2 h3 h0)). Qed.
Lemma lem1281231 (h1 : term40) (h2 : term17) (h3 : term45) (h4 : term10) : term45 = False.
Proof. exact (prop_ext (fun h5 : term45 => @lem1281230 h1 h2 h3 h4) (fun h5 : False => @lem1280470 h3)). Qed.
Lemma lem1281232 (h1 : term40) (h2 : term17) (h3 : term45) (h4 : term10) : False.
Proof. exact (EQ_MP (@lem1281231 h1 h2 h3 h4) (@lem1280470 h3)). Qed.
Lemma lem1281233 (h1 : term40) (h2 : term45) (h3 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem1281232 h1 h0 h2 h3). Qed.
Lemma lem1281234 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem1281235 (h1 : term40) (h2 : term45) (h3 : term10) : term16.
Proof. exact (EQ_MP (@lem1281234) (@lem1281233 h1 h2 h3)). Qed.
Lemma lem1281236 (h1 : term45) (h2 : term10) : term20.
Proof. exact (fun h0 : term40 => @lem1281235 h0 h1 h2). Qed.
Lemma lem1281237 (h1 : term10) : term23.
Proof. exact (fun h0 : term45 => @lem1281236 h0 h1). Qed.
Lemma lem1281238 : term25.
Proof. exact (fun h0 : term10 => @lem1281237 h0). Qed.
Lemma lem1281239 : term11.
Proof. exact (EQ_MP (@lem1280290) (@lem1281238)). Qed.
Lemma lem1281241 : term11.
Proof. exact (@lem1280046 (@lem1281239)). Qed.
Lemma lem1281242 (h1 : term10) : term22.
Proof. exact (@lem1281241 (@lem1280031 h1)). Qed.
Lemma lem1281243 (h1 : term10) : term19.
Proof. exact (@lem1281242 h1 (@lem1278399)). Qed.
Lemma lem1281244 (h1 : term10) : term15.
Proof. exact (@lem1281243 h1 (@lem1270569)). Qed.
Lemma lem1281245 (h1 : term10) : False.
Proof. exact (@lem1281244 h1 (@lem1280016)). Qed.
Lemma lem1281246 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem1281245 h1) (fun h2 : False => @lem1280031 h1)). Qed.
Lemma lem1281247 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem1281246 h1) (@lem1280031 h1)). Qed.
Lemma lem1281248 : term9.
Proof. exact (fun h0 : term10 => @lem1281247 h0). Qed.
Lemma lem1281249 : term8.
Proof. exact (EQ_MP (@lem1280030) (@lem1281248)). Qed.
