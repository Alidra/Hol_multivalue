Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_MINIMAL_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import LE_TRANS_spec.
Require Import MINIMAL_spec.
Require Import NOT_LE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
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
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem274983 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem274984 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem274985 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem274984 t1) (@lem274983 t1)). Qed.
Lemma lem274986 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem274985 t1 t2). Qed.
Lemma lem274987 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem274988 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem274987 t1 t2) (@lem274986 t1 t2)). Qed.
Lemma lem274989 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem274988 t1 t2 t3). Qed.
Lemma lem274990 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem274991 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem274990 t1 t2 t3) (@lem274989 t1 t2 t3)). Qed.
Lemma lem274992 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem274991 t1 t2 t3)). Qed.
Lemma lem274993 (P : nat -> Prop) : term7 P.
Proof. exact (@lem273176 P). Qed.
Lemma lem274994 (P : nat -> Prop) : (term7 P) = ((term8 P) = (term9 P)).
Proof. exact (eq_refl (term7 P)). Qed.
Lemma lem274997 (P : nat -> Prop) : (term8 P) = (term9 P).
Proof. exact (EQ_MP (@lem274994 P) (@lem274993 P)). Qed.
Lemma lem274998 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem274999 (P : nat -> Prop) : (term10 P) = (term11 P).
Proof. exact (MK_COMB (@lem274998) (@lem274997 P)). Qed.
Lemma lem275000 (P : nat -> Prop) (n : nat) : ((term12 n P) = (term13 P n)) = ((term12 n P) = (term13 P n)).
Proof. exact (eq_refl ((term12 n P) = (term13 P n))). Qed.
Lemma lem275001 (P : nat -> Prop) (n : nat) : (term14 P n) = (term15 P n).
Proof. exact (MK_COMB (@lem274999 P) (@lem275000 P n)). Qed.
Lemma lem275002 (P : nat -> Prop) (n : nat) : (term15 P n) = (term14 P n).
Proof. exact (SYM (@lem275001 P n)). Qed.
Lemma lem275004 (p : Prop) : p = (term16 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem275005 (P : nat -> Prop) (n : nat) : (term15 P n) = (term17 P n).
Proof. exact (@lem275004 (term15 P n)). Qed.
Lemma lem275006 (P : nat -> Prop) (n : nat) : (term17 P n) = (term15 P n).
Proof. exact (SYM (@lem275005 P n)). Qed.
Lemma lem275007 (P : nat -> Prop) (n : nat) (h1 : term18 P n) : term18 P n.
Proof. exact (h1). Qed.
Lemma lem275010 (P : nat -> Prop) (n : nat) (h1 : term19 P n) : term19 P n.
Proof. exact (h1). Qed.
Lemma lem275011 (P : nat -> Prop) (n : nat) : term20 P n.
Proof. exact (fun h0 : term19 P n => @lem275010 P n h0). Qed.
Lemma lem275012 (P : nat -> Prop) (n : nat) (h1 : term20 P n) : term20 P n.
Proof. exact (h1). Qed.
Lemma lem275013 (P : nat -> Prop) (n : nat) (h1 : term19 P n) : term19 P n.
Proof. exact (h1). Qed.
Lemma lem275014 (P : nat -> Prop) (n : nat) (h1 : term19 P n) (h2 : term20 P n) : term19 P n.
Proof. exact (@lem275012 P n h2 (@lem275013 P n h1)). Qed.
Lemma lem275015 (P : nat -> Prop) (n : nat) (h1 : term19 P n) : term21 P n.
Proof. exact (fun h0 : term20 P n => @lem275014 P n h1 h0). Qed.
Lemma lem275016 (P : nat -> Prop) (n : nat) (h1 : term20 P n) : term20 P n.
Proof. exact (h1). Qed.
Lemma lem275017 (P : nat -> Prop) (n : nat) (h1 : term19 P n) (h2 : term20 P n) : term19 P n.
Proof. exact (@lem275015 P n h1 (@lem275016 P n h2)). Qed.
Lemma lem275018 (P : nat -> Prop) (n : nat) (h1 : term20 P n) : term20 P n.
Proof. exact (fun h0 : term19 P n => @lem275017 P n h0 h1). Qed.
Lemma lem275019 (P : nat -> Prop) (n : nat) : term22 P n.
Proof. exact (fun h0 : term20 P n => @lem275018 P n h0). Qed.
Lemma lem275022 (P : nat -> Prop) (n : nat) : term20 P n.
Proof. exact (@lem275019 P n (@lem275011 P n)). Qed.
Lemma lem275068 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem275069 : term23 = term24.
Proof. exact (@lem275068 term25). Qed.
Lemma lem275078 : term26 = term26.
Proof. exact (eq_refl term26). Qed.
Lemma lem275079 : term27 = term28.
Proof. exact (MK_COMB (@lem275078) (@lem275069)). Qed.
Lemma lem275082 (P : nat -> Prop) (n : nat) : (term29 P n) = (term29 P n).
Proof. exact (eq_refl (term29 P n)). Qed.
Lemma lem275083 (P : nat -> Prop) (n : nat) : (term19 P n) = (term30 P n).
Proof. exact (MK_COMB (@lem275082 P n) (@lem275079)). Qed.
Lemma lem275086 (n : nat) : (term31 n) = (term32 n).
Proof. exact (fun_ext (fun P : nat -> Prop => @lem275083 P n)). Qed.
Lemma lem275087 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem275088 (n : nat) : (term33 n) = (term34 n).
Proof. exact (MK_COMB (@lem275087) (@lem275086 n)). Qed.
Lemma lem275093 : term35 = term36.
Proof. exact (fun_ext (fun n : nat => @lem275088 n)). Qed.
Lemma lem275094 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275103 : term37 = term38.
Proof. exact (MK_COMB (@lem275094) (@lem275093)). Qed.
Lemma lem275110 (n : nat) (m : nat) : ((term39 m n) = (Peano.lt n m)) = ((term39 m n) = (Peano.lt n m)).
Proof. exact (eq_refl ((term39 m n) = (Peano.lt n m))). Qed.
Lemma lem275111 (m : nat) : (term40 m) = (term40 m).
Proof. exact (fun_ext (fun n : nat => @lem275110 n m)). Qed.
Lemma lem275112 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275113 (m : nat) : (term41 m) = (term41 m).
Proof. exact (MK_COMB (@lem275112) (@lem275111 m)). Qed.
Lemma lem275114 : term42 = term42.
Proof. exact (fun_ext (fun m : nat => @lem275113 m)). Qed.
Lemma lem275115 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275116 : term25 = term25.
Proof. exact (MK_COMB (@lem275115) (@lem275114)). Qed.
Lemma lem275117 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem275118 : term24 = term24.
Proof. exact (MK_COMB (@lem275117) (@lem275116)). Qed.
Lemma lem275127 (n : nat) (m : nat) (p : nat) : (term43 n m p) = (term43 n m p).
Proof. exact (eq_refl (term43 n m p)). Qed.
Lemma lem275128 (n : nat) (m : nat) : (term44 n m) = (term44 n m).
Proof. exact (fun_ext (fun p : nat => @lem275127 n m p)). Qed.
Lemma lem275129 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275130 (n : nat) (m : nat) : (term45 n m) = (term45 n m).
Proof. exact (MK_COMB (@lem275129) (@lem275128 n m)). Qed.
Lemma lem275131 (m : nat) : (term46 m) = (term46 m).
Proof. exact (fun_ext (fun n : nat => @lem275130 n m)). Qed.
Lemma lem275132 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275133 (m : nat) : (term47 m) = (term47 m).
Proof. exact (MK_COMB (@lem275132) (@lem275131 m)). Qed.
Lemma lem275134 : term48 = term48.
Proof. exact (fun_ext (fun m : nat => @lem275133 m)). Qed.
Lemma lem275135 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275136 : term49 = term49.
Proof. exact (MK_COMB (@lem275135) (@lem275134)). Qed.
Lemma lem275137 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem275138 : term26 = term26.
Proof. exact (MK_COMB (@lem275137) (@lem275136)). Qed.
Lemma lem275139 : term28 = term28.
Proof. exact (MK_COMB (@lem275138) (@lem275118)). Qed.
Lemma lem275144 (P : nat -> Prop) (n : nat) (i : nat) : (term50 P n i) = (term50 P n i).
Proof. exact (eq_refl (term50 P n i)). Qed.
Lemma lem275145 (P : nat -> Prop) (n : nat) : (term51 P n) = (term51 P n).
Proof. exact (fun_ext (fun i : nat => @lem275144 P n i)). Qed.
Lemma lem275146 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275147 (P : nat -> Prop) (n : nat) : (term13 P n) = (term13 P n).
Proof. exact (MK_COMB (@lem275146) (@lem275145 P n)). Qed.
Lemma lem275150 (n : nat) (P : nat -> Prop) : (term52 n P) = (term52 n P).
Proof. exact (eq_refl (term52 n P)). Qed.
Lemma lem275151 (P : nat -> Prop) (n : nat) : ((term12 n P) = (term13 P n)) = ((term12 n P) = (term13 P n)).
Proof. exact (MK_COMB (@lem275150 n P) (@lem275147 P n)). Qed.
Lemma lem275158 (P : nat -> Prop) (m : nat) : (term53 P m) = (term53 P m).
Proof. exact (eq_refl (term53 P m)). Qed.
Lemma lem275159 (P : nat -> Prop) : (term54 P) = (term54 P).
Proof. exact (fun_ext (fun m : nat => @lem275158 P m)). Qed.
Lemma lem275160 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275161 (P : nat -> Prop) : (term55 P) = (term55 P).
Proof. exact (MK_COMB (@lem275160) (@lem275159 P)). Qed.
Lemma lem275164 (P : nat -> Prop) : (term56 P) = (term56 P).
Proof. exact (eq_refl (term56 P)). Qed.
Lemma lem275165 (P : nat -> Prop) : (term9 P) = (term9 P).
Proof. exact (MK_COMB (@lem275164 P) (@lem275161 P)). Qed.
Lemma lem275166 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem275167 (P : nat -> Prop) : (term11 P) = (term11 P).
Proof. exact (MK_COMB (@lem275166) (@lem275165 P)). Qed.
Lemma lem275168 (P : nat -> Prop) (n : nat) : (term15 P n) = (term15 P n).
Proof. exact (MK_COMB (@lem275167 P) (@lem275151 P n)). Qed.
Lemma lem275169 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem275170 (P : nat -> Prop) (n : nat) : (term18 P n) = (term18 P n).
Proof. exact (MK_COMB (@lem275169) (@lem275168 P n)). Qed.
Lemma lem275171 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem275172 (P : nat -> Prop) (n : nat) : (term29 P n) = (term29 P n).
Proof. exact (MK_COMB (@lem275171) (@lem275170 P n)). Qed.
Lemma lem275173 (P : nat -> Prop) (n : nat) : (term30 P n) = (term30 P n).
Proof. exact (MK_COMB (@lem275172 P n) (@lem275139)). Qed.
Lemma lem275174 (n : nat) : (term32 n) = (term32 n).
Proof. exact (fun_ext (fun P : nat -> Prop => @lem275173 P n)). Qed.
Lemma lem275175 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem275176 (n : nat) : (term34 n) = (term34 n).
Proof. exact (MK_COMB (@lem275175) (@lem275174 n)). Qed.
Lemma lem275177 : term36 = term36.
Proof. exact (fun_ext (fun n : nat => @lem275176 n)). Qed.
Lemma lem275178 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275179 : term38 = term38.
Proof. exact (MK_COMB (@lem275178) (@lem275177)). Qed.
Lemma lem275252 : term37 = term38.
Proof. exact (TRANS (@lem275103) (@lem275179)). Qed.
Lemma lem275253 : term38 = term37.
Proof. exact (SYM (@lem275252)). Qed.
Lemma lem275254 (P : nat -> Prop) (n : nat) (h1 : term18 P n) : term18 P n.
Proof. exact (h1). Qed.
Lemma lem275255 (h1 : term49) : term49.
Proof. exact (h1). Qed.
Lemma lem275256 (h1 : term25) : term25.
Proof. exact (h1). Qed.
Lemma lem275264 (P : nat -> Prop) (m : nat) : (term53 P m) = (term57 P m).
Proof. exact (@lem17265 (term58 m P) (term59 P m)). Qed.
Lemma lem275265 (P : nat -> Prop) : (term54 P) = (term60 P).
Proof. exact (fun_ext (fun m : nat => @lem275264 P m)). Qed.
Lemma lem275266 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275267 (P : nat -> Prop) : (term55 P) = (term61 P).
Proof. exact (MK_COMB (@lem275266) (@lem275265 P)). Qed.
Lemma lem275269 (P : nat -> Prop) : (term56 P) = (term56 P).
Proof. exact (eq_refl (term56 P)). Qed.
Lemma lem275270 (P : nat -> Prop) : (term9 P) = (term62 P).
Proof. exact (MK_COMB (@lem275269 P) (@lem275267 P)). Qed.
Lemma lem275281 (P : nat -> Prop) (n : nat) (i : nat) : (term63 P n i) = (term64 P n i).
Proof. exact (@lem17362 (P i) (Peano.le n i)). Qed.
Lemma lem275286 (P : nat -> Prop) (n : nat) (i : nat) : (term50 P n i) = (term65 P n i).
Proof. exact (@lem17265 (P i) (Peano.le n i)). Qed.
Lemma lem275287 (P : nat -> Prop) : (term66 P) = (term67 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem275288 (P : nat -> Prop) (n : nat) : (term68 P n) = (term69 P n).
Proof. exact (@lem275287 (term51 P n)). Qed.
Lemma lem275289 (P : nat -> Prop) (n : nat) (i : nat) : (term70 P n i) = (term50 P n i).
Proof. exact (eq_refl (term70 P n i)). Qed.
Lemma lem275290 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem275291 (P : nat -> Prop) (n : nat) (i : nat) : (term71 P n i) = (term63 P n i).
Proof. exact (MK_COMB (@lem275290) (@lem275289 P n i)). Qed.
Lemma lem275292 (P : nat -> Prop) (n : nat) (i : nat) : (term71 P n i) = (term64 P n i).
Proof. exact (TRANS (@lem275291 P n i) (@lem275281 P n i)). Qed.
Lemma lem275293 (P : nat -> Prop) (n : nat) : (term72 P n) = (term73 P n).
Proof. exact (fun_ext (fun i : nat => @lem275292 P n i)). Qed.
Lemma lem275294 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem275295 (P : nat -> Prop) (n : nat) : (term69 P n) = (term74 P n).
Proof. exact (MK_COMB (@lem275294) (@lem275293 P n)). Qed.
Lemma lem275296 (P : nat -> Prop) (n : nat) : (term68 P n) = (term74 P n).
Proof. exact (TRANS (@lem275288 P n) (@lem275295 P n)). Qed.
Lemma lem275297 (P : nat -> Prop) (n : nat) : (term51 P n) = (term75 P n).
Proof. exact (fun_ext (fun i : nat => @lem275286 P n i)). Qed.
Lemma lem275298 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275299 (P : nat -> Prop) (n : nat) : (term13 P n) = (term76 P n).
Proof. exact (MK_COMB (@lem275298) (@lem275297 P n)). Qed.
Lemma lem275301 (n : nat) (P : nat -> Prop) : (term77 n P) = (term77 n P).
Proof. exact (eq_refl (term77 n P)). Qed.
Lemma lem275302 (P : nat -> Prop) (n : nat) : (term78 P n) = (term79 P n).
Proof. exact (MK_COMB (@lem275301 n P) (@lem275299 P n)). Qed.
Lemma lem275304 (n : nat) (P : nat -> Prop) : (term80 n P) = (term80 n P).
Proof. exact (eq_refl (term80 n P)). Qed.
Lemma lem275305 (P : nat -> Prop) (n : nat) : (term81 P n) = (term82 P n).
Proof. exact (MK_COMB (@lem275304 n P) (@lem275296 P n)). Qed.
Lemma lem275306 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem275307 (P : nat -> Prop) (n : nat) : (term83 P n) = (term84 P n).
Proof. exact (MK_COMB (@lem275306) (@lem275305 P n)). Qed.
Lemma lem275308 (P : nat -> Prop) (n : nat) : (term85 P n) = (term86 P n).
Proof. exact (MK_COMB (@lem275307 P n) (@lem275302 P n)). Qed.
Lemma lem275309 (P : nat -> Prop) (n : nat) : (term87 P n) = (term85 P n).
Proof. exact (@lem17646 (term12 n P) (term13 P n)). Qed.
Lemma lem275310 (P : nat -> Prop) (n : nat) : (term87 P n) = (term86 P n).
Proof. exact (TRANS (@lem275309 P n) (@lem275308 P n)). Qed.
Lemma lem275311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem275312 (P : nat -> Prop) : (term88 P) = (term89 P).
Proof. exact (MK_COMB (@lem275311) (@lem275270 P)). Qed.
Lemma lem275313 (P : nat -> Prop) (n : nat) : (term90 P n) = (term91 P n).
Proof. exact (MK_COMB (@lem275312 P) (@lem275310 P n)). Qed.
Lemma lem275314 (P : nat -> Prop) (n : nat) : (term18 P n) = (term90 P n).
Proof. exact (@lem17362 (term9 P) ((term12 n P) = (term13 P n))). Qed.
Lemma lem275315 (P : nat -> Prop) (n : nat) : (term18 P n) = (term91 P n).
Proof. exact (TRANS (@lem275314 P n) (@lem275313 P n)). Qed.
Lemma lem275442 {A : Type'} (P : Prop) (Q : A -> Prop) : (term92 A P Q) = (term93 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem275443 (P : Prop) (Q : nat -> Prop) : (term94 P Q) = (term95 P Q).
Proof. exact (@lem275442 nat P Q). Qed.
Lemma lem275444 (P : nat -> Prop) (n : nat) : (term96 P n) = (term97 P n).
Proof. exact (@lem275443 (term12 n P) (term73 P n)). Qed.
Lemma lem275445 (P : nat -> Prop) (n : nat) (i : nat) : (term98 P n i) = (term64 P n i).
Proof. exact (eq_refl (term98 P n i)). Qed.
Lemma lem275446 (P : nat -> Prop) (n : nat) : (term99 P n) = (term73 P n).
Proof. exact (fun_ext (fun i : nat => @lem275445 P n i)). Qed.
Lemma lem275447 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem275448 (P : nat -> Prop) (n : nat) : (term100 P n) = (term74 P n).
Proof. exact (MK_COMB (@lem275447) (@lem275446 P n)). Qed.
Lemma lem275449 (n : nat) (P : nat -> Prop) : (term80 n P) = (term80 n P).
Proof. exact (eq_refl (term80 n P)). Qed.
Lemma lem275450 (P : nat -> Prop) (n : nat) : (term96 P n) = (term82 P n).
Proof. exact (MK_COMB (@lem275449 n P) (@lem275448 P n)). Qed.
Lemma lem275451 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem275452 (P : nat -> Prop) (n : nat) : (term101 P n) = (term102 P n).
Proof. exact (MK_COMB (@lem275451) (@lem275450 P n)). Qed.
Lemma lem275453 (P : nat -> Prop) (n : nat) (i : nat) : (term98 P n i) = (term64 P n i).
Proof. exact (eq_refl (term98 P n i)). Qed.
Lemma lem275454 (n : nat) (P : nat -> Prop) : (term80 n P) = (term80 n P).
Proof. exact (eq_refl (term80 n P)). Qed.
Lemma lem275455 (P : nat -> Prop) (n : nat) (i : nat) : (term103 P n i) = (term104 P n i).
Proof. exact (MK_COMB (@lem275454 n P) (@lem275453 P n i)). Qed.
Lemma lem275456 (P : nat -> Prop) (n : nat) : (term105 P n) = (term106 P n).
Proof. exact (fun_ext (fun i : nat => @lem275455 P n i)). Qed.
Lemma lem275457 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem275458 (P : nat -> Prop) (n : nat) : (term97 P n) = (term107 P n).
Proof. exact (MK_COMB (@lem275457) (@lem275456 P n)). Qed.
Lemma lem275459 (P : nat -> Prop) (n : nat) : ((term96 P n) = (term97 P n)) = ((term82 P n) = (term107 P n)).
Proof. exact (MK_COMB (@lem275452 P n) (@lem275458 P n)). Qed.
Lemma lem275460 (P : nat -> Prop) (n : nat) : (term82 P n) = (term107 P n).
Proof. exact (EQ_MP (@lem275459 P n) (@lem275444 P n)). Qed.
Lemma lem275461 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem275462 (P : nat -> Prop) (n : nat) : (term84 P n) = (term108 P n).
Proof. exact (MK_COMB (@lem275461) (@lem275460 P n)). Qed.
Lemma lem275463 (P : nat -> Prop) (n : nat) : (term79 P n) = (term79 P n).
Proof. exact (eq_refl (term79 P n)). Qed.
Lemma lem275464 (P : nat -> Prop) (n : nat) : (term86 P n) = (term109 P n).
Proof. exact (MK_COMB (@lem275462 P n) (@lem275463 P n)). Qed.
Lemma lem275466 {A : Type'} (P : A -> Prop) (Q : Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem275467 (P : nat -> Prop) (Q : Prop) : (term112 P Q) = (term113 P Q).
Proof. exact (@lem275466 nat P Q). Qed.
Lemma lem275468 (P : nat -> Prop) (n : nat) : (term114 P n) = (term115 P n).
Proof. exact (@lem275467 (term106 P n) (term79 P n)). Qed.
Lemma lem275469 (P : nat -> Prop) (n : nat) (i : nat) : (term116 P n i) = (term104 P n i).
Proof. exact (eq_refl (term116 P n i)). Qed.
Lemma lem275470 (P : nat -> Prop) (n : nat) : (term117 P n) = (term106 P n).
Proof. exact (fun_ext (fun i : nat => @lem275469 P n i)). Qed.
Lemma lem275471 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem275472 (P : nat -> Prop) (n : nat) : (term118 P n) = (term107 P n).
Proof. exact (MK_COMB (@lem275471) (@lem275470 P n)). Qed.
Lemma lem275473 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem275474 (P : nat -> Prop) (n : nat) : (term119 P n) = (term108 P n).
Proof. exact (MK_COMB (@lem275473) (@lem275472 P n)). Qed.
Lemma lem275475 (P : nat -> Prop) (n : nat) : (term79 P n) = (term79 P n).
Proof. exact (eq_refl (term79 P n)). Qed.
Lemma lem275476 (P : nat -> Prop) (n : nat) : (term114 P n) = (term109 P n).
Proof. exact (MK_COMB (@lem275474 P n) (@lem275475 P n)). Qed.
Lemma lem275477 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem275478 (P : nat -> Prop) (n : nat) : (term120 P n) = (term121 P n).
Proof. exact (MK_COMB (@lem275477) (@lem275476 P n)). Qed.
Lemma lem275479 (P : nat -> Prop) (n : nat) (i : nat) : (term116 P n i) = (term104 P n i).
Proof. exact (eq_refl (term116 P n i)). Qed.
Lemma lem275480 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem275481 (P : nat -> Prop) (n : nat) (i : nat) : (term122 P n i) = (term123 P n i).
Proof. exact (MK_COMB (@lem275480) (@lem275479 P n i)). Qed.
Lemma lem275482 (P : nat -> Prop) (n : nat) : (term79 P n) = (term79 P n).
Proof. exact (eq_refl (term79 P n)). Qed.
Lemma lem275483 (i : nat) (P : nat -> Prop) (n : nat) : (term124 i P n) = (term125 i P n).
Proof. exact (MK_COMB (@lem275481 P n i) (@lem275482 P n)). Qed.
Lemma lem275484 (P : nat -> Prop) (n : nat) : (term126 P n) = (term127 P n).
Proof. exact (fun_ext (fun i : nat => @lem275483 i P n)). Qed.
Lemma lem275485 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem275486 (P : nat -> Prop) (n : nat) : (term115 P n) = (term128 P n).
Proof. exact (MK_COMB (@lem275485) (@lem275484 P n)). Qed.
Lemma lem275487 (P : nat -> Prop) (n : nat) : ((term114 P n) = (term115 P n)) = ((term109 P n) = (term128 P n)).
Proof. exact (MK_COMB (@lem275478 P n) (@lem275486 P n)). Qed.
Lemma lem275488 (P : nat -> Prop) (n : nat) : (term109 P n) = (term128 P n).
Proof. exact (EQ_MP (@lem275487 P n) (@lem275468 P n)). Qed.
Lemma lem275489 (P : nat -> Prop) (n : nat) : (term86 P n) = (term128 P n).
Proof. exact (TRANS (@lem275464 P n) (@lem275488 P n)). Qed.
Lemma lem275490 (P : nat -> Prop) : (term89 P) = (term89 P).
Proof. exact (eq_refl (term89 P)). Qed.
Lemma lem275491 (P : nat -> Prop) (n : nat) : (term91 P n) = (term129 P n).
Proof. exact (MK_COMB (@lem275490 P) (@lem275489 P n)). Qed.
Lemma lem275493 {A : Type'} (P : Prop) (Q : A -> Prop) : (term92 A P Q) = (term93 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem275494 (P : Prop) (Q : nat -> Prop) : (term94 P Q) = (term95 P Q).
Proof. exact (@lem275493 nat P Q). Qed.
Lemma lem275495 (P : nat -> Prop) (n : nat) : (term130 P n) = (term131 P n).
Proof. exact (@lem275494 (term62 P) (term127 P n)). Qed.
Lemma lem275496 (i : nat) (P : nat -> Prop) (n : nat) : (term132 P n i) = (term125 i P n).
Proof. exact (eq_refl (term132 P n i)). Qed.
Lemma lem275497 (P : nat -> Prop) (n : nat) : (term133 P n) = (term127 P n).
Proof. exact (fun_ext (fun i : nat => @lem275496 i P n)). Qed.
Lemma lem275498 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem275499 (P : nat -> Prop) (n : nat) : (term134 P n) = (term128 P n).
Proof. exact (MK_COMB (@lem275498) (@lem275497 P n)). Qed.
Lemma lem275500 (P : nat -> Prop) : (term89 P) = (term89 P).
Proof. exact (eq_refl (term89 P)). Qed.
Lemma lem275501 (P : nat -> Prop) (n : nat) : (term130 P n) = (term129 P n).
Proof. exact (MK_COMB (@lem275500 P) (@lem275499 P n)). Qed.
Lemma lem275502 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem275503 (P : nat -> Prop) (n : nat) : (term135 P n) = (term136 P n).
Proof. exact (MK_COMB (@lem275502) (@lem275501 P n)). Qed.
Lemma lem275504 (i : nat) (P : nat -> Prop) (n : nat) : (term132 P n i) = (term125 i P n).
Proof. exact (eq_refl (term132 P n i)). Qed.
Lemma lem275505 (P : nat -> Prop) : (term89 P) = (term89 P).
Proof. exact (eq_refl (term89 P)). Qed.
Lemma lem275506 (i : nat) (P : nat -> Prop) (n : nat) : (term137 P n i) = (term138 i P n).
Proof. exact (MK_COMB (@lem275505 P) (@lem275504 i P n)). Qed.
Lemma lem275507 (P : nat -> Prop) (n : nat) : (term139 P n) = (term140 P n).
Proof. exact (fun_ext (fun i : nat => @lem275506 i P n)). Qed.
Lemma lem275508 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem275509 (P : nat -> Prop) (n : nat) : (term131 P n) = (term141 P n).
Proof. exact (MK_COMB (@lem275508) (@lem275507 P n)). Qed.
Lemma lem275510 (P : nat -> Prop) (n : nat) : ((term130 P n) = (term131 P n)) = ((term129 P n) = (term141 P n)).
Proof. exact (MK_COMB (@lem275503 P n) (@lem275509 P n)). Qed.
Lemma lem275511 (P : nat -> Prop) (n : nat) : (term129 P n) = (term141 P n).
Proof. exact (EQ_MP (@lem275510 P n) (@lem275495 P n)). Qed.
Lemma lem275513 (P : nat -> Prop) (n : nat) : (term91 P n) = (term141 P n).
Proof. exact (TRANS (@lem275491 P n) (@lem275511 P n)). Qed.
Lemma lem275514 (P : nat -> Prop) (n : nat) : (term18 P n) = (term141 P n).
Proof. exact (TRANS (@lem275315 P n) (@lem275513 P n)). Qed.
Lemma lem275515 (P : nat -> Prop) (n : nat) (h1 : term18 P n) : term141 P n.
Proof. exact (EQ_MP (@lem275514 P n) (@lem275254 P n h1)). Qed.
Lemma lem275522 (m : nat) (n : nat) (p : nat) : (term142 m n p) = (term143 m n p).
Proof. exact (@lem17045 (Peano.le m n) (Peano.le n p)). Qed.
Lemma lem275523 (m : nat) (p : nat) : (Peano.le m p) = (Peano.le m p).
Proof. exact (eq_refl (Peano.le m p)). Qed.
Lemma lem275524 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem275525 (m : nat) (n : nat) (p : nat) : (term144 m n p) = (term145 m n p).
Proof. exact (MK_COMB (@lem275524) (@lem275522 m n p)). Qed.
Lemma lem275526 (n : nat) (m : nat) (p : nat) : (term146 n m p) = (term147 n m p).
Proof. exact (MK_COMB (@lem275525 m n p) (@lem275523 m p)). Qed.
Lemma lem275527 (n : nat) (m : nat) (p : nat) : (term43 n m p) = (term146 n m p).
Proof. exact (@lem17265 (term148 m n p) (Peano.le m p)). Qed.
Lemma lem275528 (n : nat) (m : nat) (p : nat) : (term43 n m p) = (term147 n m p).
Proof. exact (TRANS (@lem275527 n m p) (@lem275526 n m p)). Qed.
Lemma lem275529 (n : nat) (m : nat) : (term44 n m) = (term149 n m).
Proof. exact (fun_ext (fun p : nat => @lem275528 n m p)). Qed.
Lemma lem275530 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275531 (n : nat) (m : nat) : (term45 n m) = (term150 n m).
Proof. exact (MK_COMB (@lem275530) (@lem275529 n m)). Qed.
Lemma lem275532 (m : nat) : (term46 m) = (term151 m).
Proof. exact (fun_ext (fun n : nat => @lem275531 n m)). Qed.
Lemma lem275533 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275534 (m : nat) : (term47 m) = (term152 m).
Proof. exact (MK_COMB (@lem275533) (@lem275532 m)). Qed.
Lemma lem275535 : term48 = term153.
Proof. exact (fun_ext (fun m : nat => @lem275534 m)). Qed.
Lemma lem275536 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275597 : term49 = term154.
Proof. exact (MK_COMB (@lem275536) (@lem275535)). Qed.
Lemma lem275598 (h1 : term49) : term154.
Proof. exact (EQ_MP (@lem275597) (@lem275255 h1)). Qed.
Lemma lem275602 (m : nat) (n : nat) : (term155 m n) = (Peano.le m n).
Proof. exact (@lem16933 (Peano.le m n)). Qed.
Lemma lem275604 (n : nat) (m : nat) : (Peano.lt n m) = (Peano.lt n m).
Proof. exact (eq_refl (Peano.lt n m)). Qed.
Lemma lem275605 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem275606 (m : nat) (n : nat) : (term156 m n) = (term157 m n).
Proof. exact (MK_COMB (@lem275605) (@lem275602 m n)). Qed.
Lemma lem275607 (n : nat) (m : nat) : (term158 n m) = (term159 n m).
Proof. exact (MK_COMB (@lem275606 m n) (@lem275604 n m)). Qed.
Lemma lem275612 (n : nat) (m : nat) : (term160 n m) = (term160 n m).
Proof. exact (eq_refl (term160 n m)). Qed.
Lemma lem275613 (n : nat) (m : nat) : (term161 n m) = (term162 n m).
Proof. exact (MK_COMB (@lem275612 n m) (@lem275607 n m)). Qed.
Lemma lem275614 (n : nat) (m : nat) : ((term39 m n) = (Peano.lt n m)) = (term161 n m).
Proof. exact (@lem17784 (term39 m n) (Peano.lt n m)). Qed.
Lemma lem275615 (n : nat) (m : nat) : ((term39 m n) = (Peano.lt n m)) = (term162 n m).
Proof. exact (TRANS (@lem275614 n m) (@lem275613 n m)). Qed.
Lemma lem275616 (m : nat) : (term40 m) = (term163 m).
Proof. exact (fun_ext (fun n : nat => @lem275615 n m)). Qed.
Lemma lem275617 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275618 (m : nat) : (term41 m) = (term164 m).
Proof. exact (MK_COMB (@lem275617) (@lem275616 m)). Qed.
Lemma lem275619 : term42 = term165.
Proof. exact (fun_ext (fun m : nat => @lem275618 m)). Qed.
Lemma lem275620 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275621 : term25 = term166.
Proof. exact (MK_COMB (@lem275620) (@lem275619)). Qed.
Lemma lem275627 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem275628 (P : nat -> Prop) (Q : nat -> Prop) : (term169 P Q) = (term170 P Q).
Proof. exact (@lem275627 nat P Q). Qed.
Lemma lem275629 (m : nat) : (term171 m) = (term172 m).
Proof. exact (@lem275628 (term173 m) (term174 m)). Qed.
Lemma lem275630 (n : nat) (m : nat) : (term175 m n) = (term176 n m).
Proof. exact (eq_refl (term175 m n)). Qed.
Lemma lem275631 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem275632 (n : nat) (m : nat) : (term177 m n) = (term160 n m).
Proof. exact (MK_COMB (@lem275631) (@lem275630 n m)). Qed.
Lemma lem275633 (n : nat) (m : nat) : (term178 m n) = (term159 n m).
Proof. exact (eq_refl (term178 m n)). Qed.
Lemma lem275634 (n : nat) (m : nat) : (term179 m n) = (term162 n m).
Proof. exact (MK_COMB (@lem275632 n m) (@lem275633 n m)). Qed.
Lemma lem275635 (m : nat) : (term180 m) = (term163 m).
Proof. exact (fun_ext (fun n : nat => @lem275634 n m)). Qed.
Lemma lem275636 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275637 (m : nat) : (term171 m) = (term164 m).
Proof. exact (MK_COMB (@lem275636) (@lem275635 m)). Qed.
Lemma lem275638 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem275639 (m : nat) : (term181 m) = (term182 m).
Proof. exact (MK_COMB (@lem275638) (@lem275637 m)). Qed.
Lemma lem275640 (n : nat) (m : nat) : (term175 m n) = (term176 n m).
Proof. exact (eq_refl (term175 m n)). Qed.
Lemma lem275641 (m : nat) : (term183 m) = (term173 m).
Proof. exact (fun_ext (fun n : nat => @lem275640 n m)). Qed.
Lemma lem275642 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275643 (m : nat) : (term184 m) = (term185 m).
Proof. exact (MK_COMB (@lem275642) (@lem275641 m)). Qed.
Lemma lem275644 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem275645 (m : nat) : (term186 m) = (term187 m).
Proof. exact (MK_COMB (@lem275644) (@lem275643 m)). Qed.
Lemma lem275646 (n : nat) (m : nat) : (term178 m n) = (term159 n m).
Proof. exact (eq_refl (term178 m n)). Qed.
Lemma lem275647 (m : nat) : (term188 m) = (term174 m).
Proof. exact (fun_ext (fun n : nat => @lem275646 n m)). Qed.
Lemma lem275648 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275649 (m : nat) : (term189 m) = (term190 m).
Proof. exact (MK_COMB (@lem275648) (@lem275647 m)). Qed.
Lemma lem275650 (m : nat) : (term172 m) = (term191 m).
Proof. exact (MK_COMB (@lem275645 m) (@lem275649 m)). Qed.
Lemma lem275651 (m : nat) : ((term171 m) = (term172 m)) = ((term164 m) = (term191 m)).
Proof. exact (MK_COMB (@lem275639 m) (@lem275650 m)). Qed.
Lemma lem275652 (m : nat) : (term164 m) = (term191 m).
Proof. exact (EQ_MP (@lem275651 m) (@lem275629 m)). Qed.
Lemma lem275749 : term165 = term192.
Proof. exact (fun_ext (fun m : nat => @lem275652 m)). Qed.
Lemma lem275750 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275751 : term166 = term193.
Proof. exact (MK_COMB (@lem275750) (@lem275749)). Qed.
Lemma lem275753 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem275754 (P : nat -> Prop) (Q : nat -> Prop) : (term169 P Q) = (term170 P Q).
Proof. exact (@lem275753 nat P Q). Qed.
Lemma lem275755 : term194 = term195.
Proof. exact (@lem275754 term196 term197). Qed.
Lemma lem275756 (m : nat) : (term198 m) = (term185 m).
Proof. exact (eq_refl (term198 m)). Qed.
Lemma lem275757 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem275758 (m : nat) : (term199 m) = (term187 m).
Proof. exact (MK_COMB (@lem275757) (@lem275756 m)). Qed.
Lemma lem275759 (m : nat) : (term200 m) = (term190 m).
Proof. exact (eq_refl (term200 m)). Qed.
Lemma lem275760 (m : nat) : (term201 m) = (term191 m).
Proof. exact (MK_COMB (@lem275758 m) (@lem275759 m)). Qed.
Lemma lem275761 : term202 = term192.
Proof. exact (fun_ext (fun m : nat => @lem275760 m)). Qed.
Lemma lem275762 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275763 : term194 = term193.
Proof. exact (MK_COMB (@lem275762) (@lem275761)). Qed.
Lemma lem275764 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem275765 : term203 = term204.
Proof. exact (MK_COMB (@lem275764) (@lem275763)). Qed.
Lemma lem275766 (m : nat) : (term198 m) = (term185 m).
Proof. exact (eq_refl (term198 m)). Qed.
Lemma lem275767 : term205 = term196.
Proof. exact (fun_ext (fun m : nat => @lem275766 m)). Qed.
Lemma lem275768 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275769 : term206 = term207.
Proof. exact (MK_COMB (@lem275768) (@lem275767)). Qed.
Lemma lem275770 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem275771 : term208 = term209.
Proof. exact (MK_COMB (@lem275770) (@lem275769)). Qed.
Lemma lem275772 (m : nat) : (term200 m) = (term190 m).
Proof. exact (eq_refl (term200 m)). Qed.
Lemma lem275773 : term210 = term197.
Proof. exact (fun_ext (fun m : nat => @lem275772 m)). Qed.
Lemma lem275774 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275775 : term211 = term212.
Proof. exact (MK_COMB (@lem275774) (@lem275773)). Qed.
Lemma lem275776 : term195 = term213.
Proof. exact (MK_COMB (@lem275771) (@lem275775)). Qed.
Lemma lem275777 : (term194 = term195) = (term193 = term213).
Proof. exact (MK_COMB (@lem275765) (@lem275776)). Qed.
Lemma lem275778 : term193 = term213.
Proof. exact (EQ_MP (@lem275777) (@lem275755)). Qed.
Lemma lem275885 : term166 = term213.
Proof. exact (TRANS (@lem275751) (@lem275778)). Qed.
Lemma lem275886 : term25 = term213.
Proof. exact (TRANS (@lem275621) (@lem275885)). Qed.
Lemma lem275887 (h1 : term25) : term213.
Proof. exact (EQ_MP (@lem275886) (@lem275256 h1)). Qed.
Lemma lem275888 (i : nat) (P : nat -> Prop) (n : nat) (h1 : term138 i P n) : term138 i P n.
Proof. exact (h1). Qed.
Lemma lem275913 (n : nat) (m : nat) (p : nat) : (term147 n m p) = (term147 n m p).
Proof. exact (eq_refl (term147 n m p)). Qed.
Lemma lem275914 (n : nat) (m : nat) : (term149 n m) = (term149 n m).
Proof. exact (fun_ext (fun p : nat => @lem275913 n m p)). Qed.
Lemma lem275915 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275916 (n : nat) (m : nat) : (term150 n m) = (term150 n m).
Proof. exact (MK_COMB (@lem275915) (@lem275914 n m)). Qed.
Lemma lem275917 (m : nat) : (term151 m) = (term151 m).
Proof. exact (fun_ext (fun n : nat => @lem275916 n m)). Qed.
Lemma lem275918 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275919 (m : nat) : (term152 m) = (term152 m).
Proof. exact (MK_COMB (@lem275918) (@lem275917 m)). Qed.
Lemma lem275920 : term153 = term153.
Proof. exact (fun_ext (fun m : nat => @lem275919 m)). Qed.
Lemma lem275921 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275922 : term154 = term154.
Proof. exact (MK_COMB (@lem275921) (@lem275920)). Qed.
Lemma lem275923 (h1 : term49) : term154.
Proof. exact (EQ_MP (@lem275922) (@lem275598 h1)). Qed.
Lemma lem275936 (n : nat) (m : nat) : (term159 n m) = (term159 n m).
Proof. exact (eq_refl (term159 n m)). Qed.
Lemma lem275937 (m : nat) : (term174 m) = (term174 m).
Proof. exact (fun_ext (fun n : nat => @lem275936 n m)). Qed.
Lemma lem275938 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275939 (m : nat) : (term190 m) = (term190 m).
Proof. exact (MK_COMB (@lem275938) (@lem275937 m)). Qed.
Lemma lem275940 : term197 = term197.
Proof. exact (fun_ext (fun m : nat => @lem275939 m)). Qed.
Lemma lem275941 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275942 : term212 = term212.
Proof. exact (MK_COMB (@lem275941) (@lem275940)). Qed.
Lemma lem275959 (n : nat) (m : nat) : (term176 n m) = (term176 n m).
Proof. exact (eq_refl (term176 n m)). Qed.
Lemma lem275960 (m : nat) : (term173 m) = (term173 m).
Proof. exact (fun_ext (fun n : nat => @lem275959 n m)). Qed.
Lemma lem275961 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275962 (m : nat) : (term185 m) = (term185 m).
Proof. exact (MK_COMB (@lem275961) (@lem275960 m)). Qed.
Lemma lem275963 : term196 = term196.
Proof. exact (fun_ext (fun m : nat => @lem275962 m)). Qed.
Lemma lem275964 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275965 : term207 = term207.
Proof. exact (MK_COMB (@lem275964) (@lem275963)). Qed.
Lemma lem275966 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem275967 : term209 = term209.
Proof. exact (MK_COMB (@lem275966) (@lem275965)). Qed.
Lemma lem275968 : term213 = term213.
Proof. exact (MK_COMB (@lem275967) (@lem275942)). Qed.
Lemma lem275969 (h1 : term25) : term213.
Proof. exact (EQ_MP (@lem275968) (@lem275887 h1)). Qed.
Lemma lem275974 (n : nat) (i : nat) : (Peano.le n i) = (Peano.le n i).
Proof. exact (eq_refl (Peano.le n i)). Qed.
Lemma lem275975 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem275980 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem275981 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem275980 nat Prop f x). Qed.
Lemma lem275983 (P : nat -> Prop) (i : nat) : (P i) = (@I (nat -> Prop) P i).
Proof. exact (@lem275981 P i). Qed.
Lemma lem275984 (P : nat -> Prop) (i : nat) : (term59 P i) = (term214 P i).
Proof. exact (MK_COMB (@lem275975) (@lem275983 P i)). Qed.
Lemma lem275985 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem275986 (P : nat -> Prop) (i : nat) : (term215 P i) = (term216 P i).
Proof. exact (MK_COMB (@lem275985) (@lem275984 P i)). Qed.
Lemma lem275987 (P : nat -> Prop) (n : nat) (i : nat) : (term65 P n i) = (term217 P n i).
Proof. exact (MK_COMB (@lem275986 P i) (@lem275974 n i)). Qed.
Lemma lem275988 (P : nat -> Prop) (n : nat) : (term75 P n) = (term218 P n).
Proof. exact (fun_ext (fun i : nat => @lem275987 P n i)). Qed.
Lemma lem275989 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem275990 (P : nat -> Prop) (n : nat) : (term76 P n) = (term219 P n).
Proof. exact (MK_COMB (@lem275989) (@lem275988 P n)). Qed.
Lemma lem276001 (n : nat) (P : nat -> Prop) : (term77 n P) = (term77 n P).
Proof. exact (eq_refl (term77 n P)). Qed.
Lemma lem276002 (P : nat -> Prop) (n : nat) : (term79 P n) = (term220 P n).
Proof. exact (MK_COMB (@lem276001 n P) (@lem275990 P n)). Qed.
Lemma lem276009 (n : nat) (i : nat) : (term39 n i) = (term39 n i).
Proof. exact (eq_refl (term39 n i)). Qed.
Lemma lem276014 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem276015 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem276014 nat Prop f x). Qed.
Lemma lem276017 (P : nat -> Prop) (i : nat) : (P i) = (@I (nat -> Prop) P i).
Proof. exact (@lem276015 P i). Qed.
Lemma lem276018 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem276019 (P : nat -> Prop) (i : nat) : (term221 P i) = (term222 P i).
Proof. exact (MK_COMB (@lem276018) (@lem276017 P i)). Qed.
Lemma lem276020 (P : nat -> Prop) (n : nat) (i : nat) : (term64 P n i) = (term223 P n i).
Proof. exact (MK_COMB (@lem276019 P i) (@lem276009 n i)). Qed.
Lemma lem276029 (n : nat) (P : nat -> Prop) : (term80 n P) = (term80 n P).
Proof. exact (eq_refl (term80 n P)). Qed.
Lemma lem276030 (P : nat -> Prop) (n : nat) (i : nat) : (term104 P n i) = (term224 P n i).
Proof. exact (MK_COMB (@lem276029 n P) (@lem276020 P n i)). Qed.
Lemma lem276031 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem276032 (P : nat -> Prop) (n : nat) (i : nat) : (term123 P n i) = (term225 P n i).
Proof. exact (MK_COMB (@lem276031) (@lem276030 P n i)). Qed.
Lemma lem276033 (i : nat) (P : nat -> Prop) (n : nat) : (term125 i P n) = (term226 i P n).
Proof. exact (MK_COMB (@lem276032 P n i) (@lem276002 P n)). Qed.
Lemma lem276034 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem276039 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem276040 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem276039 nat Prop f x). Qed.
Lemma lem276042 (P : nat -> Prop) (m : nat) : (P m) = (@I (nat -> Prop) P m).
Proof. exact (@lem276040 P m). Qed.
Lemma lem276043 (P : nat -> Prop) (m : nat) : (term59 P m) = (term214 P m).
Proof. exact (MK_COMB (@lem276034) (@lem276042 P m)). Qed.
Lemma lem276054 (m : nat) (P : nat -> Prop) : (term227 m P) = (term227 m P).
Proof. exact (eq_refl (term227 m P)). Qed.
Lemma lem276055 (P : nat -> Prop) (m : nat) : (term57 P m) = (term228 P m).
Proof. exact (MK_COMB (@lem276054 m P) (@lem276043 P m)). Qed.
Lemma lem276056 (P : nat -> Prop) : (term60 P) = (term229 P).
Proof. exact (fun_ext (fun m : nat => @lem276055 P m)). Qed.
Lemma lem276057 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem276058 (P : nat -> Prop) : (term61 P) = (term230 P).
Proof. exact (MK_COMB (@lem276057) (@lem276056 P)). Qed.
Lemma lem276065 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem276066 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem276065 nat Prop f x). Qed.
Lemma lem276068 (P : nat -> Prop) : (term231 P) = (term232 P).
Proof. exact (@lem276066 P (minimal P)). Qed.
Lemma lem276069 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem276070 (P : nat -> Prop) : (term56 P) = (term233 P).
Proof. exact (MK_COMB (@lem276069) (@lem276068 P)). Qed.
Lemma lem276071 (P : nat -> Prop) : (term62 P) = (term234 P).
Proof. exact (MK_COMB (@lem276070 P) (@lem276058 P)). Qed.
Lemma lem276072 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem276073 (P : nat -> Prop) : (term89 P) = (term235 P).
Proof. exact (MK_COMB (@lem276072) (@lem276071 P)). Qed.
Lemma lem276074 (i : nat) (P : nat -> Prop) (n : nat) : (term138 i P n) = (term236 i P n).
Proof. exact (MK_COMB (@lem276073 P) (@lem276033 i P n)). Qed.
Lemma lem276075 (i : nat) (P : nat -> Prop) (n : nat) (h1 : term138 i P n) : term236 i P n.
Proof. exact (EQ_MP (@lem276074 i P n) (@lem275888 i P n h1)). Qed.
Lemma lem276076 (i : nat) (P : nat -> Prop) (n : nat) (h1 : term138 i P n) : term226 i P n.
Proof. exact (proj2 (@lem276075 i P n h1)). Qed.
Lemma lem276077 (i : nat) (P : nat -> Prop) (n : nat) (h1 : term138 i P n) : term234 P.
Proof. exact (proj1 (@lem276075 i P n h1)). Qed.
Lemma lem276078 (i : nat) (P : nat -> Prop) (n : nat) (h1 : term138 i P n) : term230 P.
Proof. exact (proj2 (@lem276077 i P n h1)). Qed.
Lemma lem276080 (h1 : term25) : term212.
Proof. exact (proj2 (@lem275969 h1)). Qed.
Lemma lem276082 (P : nat -> Prop) (n : nat) (i : nat) (h1 : term224 P n i) : term224 P n i.
Proof. exact (h1). Qed.
Lemma lem276083 (P : nat -> Prop) (n : nat) (h1 : term220 P n) : term220 P n.
Proof. exact (h1). Qed.
Lemma lem276084 (P : nat -> Prop) (n : nat) (i : nat) (h1 : term224 P n i) : term223 P n i.
Proof. exact (proj2 (@lem276082 P n i h1)). Qed.
Lemma lem276088 (P : nat -> Prop) (n : nat) (h1 : term220 P n) : term219 P n.
Proof. exact (proj2 (@lem276083 P n h1)). Qed.
Lemma lem276103 (n : nat) (m : nat) (p : nat) : (term147 n m p) = (term147 n m p).
Proof. exact (eq_refl (term147 n m p)). Qed.
Lemma lem276104 (n : nat) (m : nat) : (term149 n m) = (term149 n m).
Proof. exact (fun_ext (fun p : nat => @lem276103 n m p)). Qed.
Lemma lem276105 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem276106 (n : nat) (m : nat) : (term150 n m) = (term150 n m).
Proof. exact (MK_COMB (@lem276105) (@lem276104 n m)). Qed.
Lemma lem276107 (m : nat) : (term151 m) = (term151 m).
Proof. exact (fun_ext (fun n : nat => @lem276106 n m)). Qed.
Lemma lem276108 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem276109 (m : nat) : (term152 m) = (term152 m).
Proof. exact (MK_COMB (@lem276108) (@lem276107 m)). Qed.
Lemma lem276110 : term153 = term153.
Proof. exact (fun_ext (fun m : nat => @lem276109 m)). Qed.
Lemma lem276111 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem276113 : term154 = term154.
Proof. exact (MK_COMB (@lem276111) (@lem276110)). Qed.
Lemma lem276114 (h1 : term49) : term154.
Proof. exact (EQ_MP (@lem276113) (@lem275923 h1)). Qed.
Lemma lem276126 (P : nat -> Prop) (m : nat) : (term228 P m) = (term228 P m).
Proof. exact (eq_refl (term228 P m)). Qed.
Lemma lem276127 (P : nat -> Prop) : (term229 P) = (term229 P).
Proof. exact (fun_ext (fun m : nat => @lem276126 P m)). Qed.
Lemma lem276128 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem276130 (P : nat -> Prop) : (term230 P) = (term230 P).
Proof. exact (MK_COMB (@lem276128) (@lem276127 P)). Qed.
Lemma lem276131 (i : nat) (P : nat -> Prop) (n : nat) (h1 : term138 i P n) : term230 P.
Proof. exact (EQ_MP (@lem276130 P) (@lem276078 i P n h1)). Qed.
Lemma lem276155 (n : nat) (m : nat) : (term159 n m) = (term159 n m).
Proof. exact (eq_refl (term159 n m)). Qed.
Lemma lem276156 (m : nat) : (term174 m) = (term174 m).
Proof. exact (fun_ext (fun n : nat => @lem276155 n m)). Qed.
Lemma lem276157 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem276158 (m : nat) : (term190 m) = (term190 m).
Proof. exact (MK_COMB (@lem276157) (@lem276156 m)). Qed.
Lemma lem276159 : term197 = term197.
Proof. exact (fun_ext (fun m : nat => @lem276158 m)). Qed.
Lemma lem276160 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem276162 : term212 = term212.
Proof. exact (MK_COMB (@lem276160) (@lem276159)). Qed.
Lemma lem276163 (h1 : term25) : term212.
Proof. exact (EQ_MP (@lem276162) (@lem276080 h1)). Qed.
Lemma lem276261 (P : nat -> Prop) (n : nat) (i : nat) : (term217 P n i) = (term217 P n i).
Proof. exact (eq_refl (term217 P n i)). Qed.
Lemma lem276262 (P : nat -> Prop) (n : nat) : (term218 P n) = (term218 P n).
Proof. exact (fun_ext (fun i : nat => @lem276261 P n i)). Qed.
Lemma lem276263 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem276265 (P : nat -> Prop) (n : nat) : (term219 P n) = (term219 P n).
Proof. exact (MK_COMB (@lem276263) (@lem276262 P n)). Qed.
Lemma lem276266 (P : nat -> Prop) (n : nat) (h1 : term220 P n) : term219 P n.
Proof. exact (EQ_MP (@lem276265 P n) (@lem276088 P n h1)). Qed.
Lemma lem276267 (_6428 : nat) (h1 : term49) : term237 _6428.
Proof. exact (@lem276114 h1 _6428). Qed.
Lemma lem276268 (_6428 : nat) : (term237 _6428) = (term152 _6428).
Proof. exact (eq_refl (term237 _6428)). Qed.
Lemma lem276269 (_6428 : nat) (h1 : term49) : term152 _6428.
Proof. exact (EQ_MP (@lem276268 _6428) (@lem276267 _6428 h1)). Qed.
Lemma lem276270 (_6428 : nat) (_6429 : nat) (h1 : term49) : term238 _6428 _6429.
Proof. exact (@lem276269 _6428 h1 _6429). Qed.
Lemma lem276271 (_6429 : nat) (_6428 : nat) : (term238 _6428 _6429) = (term150 _6429 _6428).
Proof. exact (eq_refl (term238 _6428 _6429)). Qed.
Lemma lem276272 (_6429 : nat) (_6428 : nat) (h1 : term49) : term150 _6429 _6428.
Proof. exact (EQ_MP (@lem276271 _6429 _6428) (@lem276270 _6428 _6429 h1)). Qed.
Lemma lem276273 (_6429 : nat) (_6428 : nat) (_6430 : nat) (h1 : term49) : term239 _6429 _6428 _6430.
Proof. exact (@lem276272 _6429 _6428 h1 _6430). Qed.
Lemma lem276274 (_6429 : nat) (_6428 : nat) (_6430 : nat) : (term239 _6429 _6428 _6430) = (term147 _6429 _6428 _6430).
Proof. exact (eq_refl (term239 _6429 _6428 _6430)). Qed.
Lemma lem276275 (_6429 : nat) (_6428 : nat) (_6430 : nat) (h1 : term49) : term147 _6429 _6428 _6430.
Proof. exact (EQ_MP (@lem276274 _6429 _6428 _6430) (@lem276273 _6429 _6428 _6430 h1)). Qed.
Lemma lem276276 (_6431 : nat) (i : nat) (P : nat -> Prop) (n : nat) (h1 : term138 i P n) : term240 P _6431.
Proof. exact (@lem276131 i P n h1 _6431). Qed.
Lemma lem276277 (P : nat -> Prop) (_6431 : nat) : (term240 P _6431) = (term228 P _6431).
Proof. exact (eq_refl (term240 P _6431)). Qed.
Lemma lem276285 (_6434 : nat) (h1 : term25) : term200 _6434.
Proof. exact (@lem276163 h1 _6434). Qed.
Lemma lem276286 (_6434 : nat) : (term200 _6434) = (term190 _6434).
Proof. exact (eq_refl (term200 _6434)). Qed.
Lemma lem276287 (_6434 : nat) (h1 : term25) : term190 _6434.
Proof. exact (EQ_MP (@lem276286 _6434) (@lem276285 _6434 h1)). Qed.
Lemma lem276288 (_6434 : nat) (_6435 : nat) (h1 : term25) : term178 _6434 _6435.
Proof. exact (@lem276287 _6434 h1 _6435). Qed.
Lemma lem276289 (_6435 : nat) (_6434 : nat) : (term178 _6434 _6435) = (term159 _6435 _6434).
Proof. exact (eq_refl (term178 _6434 _6435)). Qed.
Lemma lem276315 (_6444 : nat) (P : nat -> Prop) (n : nat) (h1 : term220 P n) : term241 P n _6444.
Proof. exact (@lem276266 P n h1 _6444). Qed.
Lemma lem276316 (P : nat -> Prop) (n : nat) (_6444 : nat) : (term241 P n _6444) = (term217 P n _6444).
Proof. exact (eq_refl (term241 P n _6444)). Qed.
Lemma lem276328 (_6429 : nat) (_6428 : nat) (_6430 : nat) : (term147 _6429 _6428 _6430) = (term242 _6429 _6428 _6430).
Proof. exact (@lem274992 (term39 _6428 _6429) (term39 _6429 _6430) (Peano.le _6428 _6430)). Qed.
Lemma lem276329 (_6429 : nat) (_6428 : nat) (_6430 : nat) (h1 : term49) : term242 _6429 _6428 _6430.
Proof. exact (EQ_MP (@lem276328 _6429 _6428 _6430) (@lem276275 _6429 _6428 _6430 h1)). Qed.
Lemma lem276337 (_6431 : nat) (i : nat) (P : nat -> Prop) (n : nat) (h1 : term138 i P n) : term228 P _6431.
Proof. exact (EQ_MP (@lem276277 P _6431) (@lem276276 _6431 i P n h1)). Qed.
Lemma lem276349 (_6435 : nat) (_6434 : nat) (h1 : term25) : term159 _6435 _6434.
Proof. exact (EQ_MP (@lem276289 _6435 _6434) (@lem276288 _6434 _6435 h1)). Qed.
Lemma lem276355 (P : nat -> Prop) (n : nat) (i : nat) (h1 : term224 P n i) : term39 n i.
Proof. exact (proj2 (@lem276084 P n i h1)). Qed.
Lemma lem276389 (P : nat -> Prop) (n : nat) (h1 : term220 P n) : term243 n P.
Proof. exact (proj1 (@lem276083 P n h1)). Qed.
Lemma lem276395 (_6444 : nat) (P : nat -> Prop) (n : nat) (h1 : term220 P n) : term217 P n _6444.
Proof. exact (EQ_MP (@lem276316 P n _6444) (@lem276315 _6444 P n h1)). Qed.
Lemma lem276397 (P : nat -> Prop) (n : nat) (i : nat) (h1 : term224 P n i) : term12 n P.
Proof. exact (proj1 (@lem276082 P n i h1)). Qed.
Lemma lem276398 (P : nat -> Prop) (n : nat) (i : nat) (h1 : term224 P n i) : term244 n P.
Proof. exact (fun h0 : term243 n P => @lem276397 P n i h1). Qed.
Lemma lem276400 (p : Prop) : (term245 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem276401 (n : nat) (P : nat -> Prop) : (term244 n P) = (term12 n P).
Proof. exact (@lem276400 (term12 n P)). Qed.
Lemma lem276402 (P : nat -> Prop) (n : nat) (i : nat) (h1 : term224 P n i) : term12 n P.
Proof. exact (EQ_MP (@lem276401 n P) (@lem276398 P n i h1)). Qed.
Lemma lem276404 (P : nat -> Prop) (n : nat) (i : nat) (h1 : term224 P n i) : @I (nat -> Prop) P i.
Proof. exact (proj1 (@lem276084 P n i h1)). Qed.
Lemma lem276405 (P : nat -> Prop) (n : nat) (i : nat) (h1 : term224 P n i) : term246 P i.
Proof. exact (fun h0 : term214 P i => @lem276404 P n i h1). Qed.
Lemma lem276407 (p : Prop) : (term245 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem276408 (P : nat -> Prop) (i : nat) : (term246 P i) = (@I (nat -> Prop) P i).
Proof. exact (@lem276407 (@I (nat -> Prop) P i)). Qed.
Lemma lem276409 (P : nat -> Prop) (n : nat) (i : nat) (h1 : term224 P n i) : @I (nat -> Prop) P i.
Proof. exact (EQ_MP (@lem276408 P i) (@lem276405 P n i h1)). Qed.
Lemma lem276411 (b : Prop) (a : Prop) : (a \/ b) = (term247 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem276412 (_6431 : nat) (P : nat -> Prop) : (term228 P _6431) = (term248 _6431 P).
Proof. exact (@lem276411 (term214 P _6431) (term249 _6431 P)). Qed.
Lemma lem276414 (a : Prop) : (term250 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem276415 (P : nat -> Prop) (_6431 : nat) : (term251 P _6431) = (@I (nat -> Prop) P _6431).
Proof. exact (@lem276414 (@I (nat -> Prop) P _6431)). Qed.
Lemma lem276416 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem276417 (P : nat -> Prop) (_6431 : nat) : (term252 P _6431) = (term253 P _6431).
Proof. exact (MK_COMB (@lem276416) (@lem276415 P _6431)). Qed.
Lemma lem276418 (_6431 : nat) (P : nat -> Prop) : (term249 _6431 P) = (term249 _6431 P).
Proof. exact (eq_refl (term249 _6431 P)). Qed.
Lemma lem276419 (_6431 : nat) (P : nat -> Prop) : (term248 _6431 P) = (term254 _6431 P).
Proof. exact (MK_COMB (@lem276417 P _6431) (@lem276418 _6431 P)). Qed.
Lemma lem276420 (_6431 : nat) (P : nat -> Prop) : (term228 P _6431) = (term254 _6431 P).
Proof. exact (TRANS (@lem276412 _6431 P) (@lem276419 _6431 P)). Qed.
Lemma lem276423 (_6431 : nat) (i : nat) (P : nat -> Prop) (n : nat) (h1 : term138 i P n) : term254 _6431 P.
Proof. exact (EQ_MP (@lem276420 _6431 P) (@lem276337 _6431 i P n h1)). Qed.
Lemma lem276424 (i : nat) (P : nat -> Prop) (n : nat) (h1 : term138 i P n) : term254 i P.
Proof. exact (@lem276423 i i P n h1). Qed.
Lemma lem276427 (P : nat -> Prop) (n : nat) (i : nat) (h1 : term138 i P n) (h2 : term224 P n i) : term249 i P.
Proof. exact (@lem276424 i P n h1 (@lem276409 P n i h2)). Qed.
Lemma lem276428 (P : nat -> Prop) (n : nat) (i : nat) (h1 : term138 i P n) (h2 : term224 P n i) : term255 i P.
Proof. exact (fun h0 : term58 i P => @lem276427 P n i h1 h2). Qed.
Lemma lem276430 (p : Prop) : (term256 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem276431 (i : nat) (P : nat -> Prop) : (term255 i P) = (term249 i P).
Proof. exact (@lem276430 (term58 i P)). Qed.
Lemma lem276432 (P : nat -> Prop) (n : nat) (i : nat) (h1 : term138 i P n) (h2 : term224 P n i) : term249 i P.
Proof. exact (EQ_MP (@lem276431 i P) (@lem276428 P n i h1 h2)). Qed.
Lemma lem276434 (b : Prop) (a : Prop) : (a \/ b) = (term247 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem276437 (_6434 : nat) (_6435 : nat) : (term159 _6435 _6434) = (term257 _6434 _6435).
Proof. exact (@lem276434 (Peano.lt _6435 _6434) (Peano.le _6434 _6435)). Qed.
Lemma lem276440 (_6434 : nat) (_6435 : nat) (h1 : term25) : term257 _6434 _6435.
Proof. exact (EQ_MP (@lem276437 _6434 _6435) (@lem276349 _6435 _6434 h1)). Qed.
Lemma lem276441 (P : nat -> Prop) (i : nat) (h1 : term25) : term258 P i.
Proof. exact (@lem276440 (minimal P) i h1). Qed.
Lemma lem276444 (P : nat -> Prop) (n : nat) (i : nat) (h1 : term25) (h2 : term138 i P n) (h3 : term224 P n i) : term259 P i.
Proof. exact (@lem276441 P i h1 (@lem276432 P n i h2 h3)). Qed.
Lemma lem276445 (P : nat -> Prop) (n : nat) (i : nat) (h1 : term25) (h2 : term138 i P n) (h3 : term224 P n i) : term260 P i.
Proof. exact (fun h0 : term261 P i => @lem276444 P n i h1 h2 h3). Qed.
Lemma lem276447 (p : Prop) : (term245 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem276448 (P : nat -> Prop) (i : nat) : (term260 P i) = (term259 P i).
Proof. exact (@lem276447 (term259 P i)). Qed.
Lemma lem276449 (P : nat -> Prop) (n : nat) (i : nat) (h1 : term25) (h2 : term138 i P n) (h3 : term224 P n i) : term259 P i.
Proof. exact (EQ_MP (@lem276448 P i) (@lem276445 P n i h1 h2 h3)). Qed.
Lemma lem276465 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem276466 (_6428 : nat) (_6429 : nat) (_6430 : nat) : (term262 _6429 _6428 _6430) = (term263 _6428 _6429 _6430).
Proof. exact (@lem276465 (Peano.le _6428 _6430) (term39 _6429 _6430)). Qed.
Lemma lem276472 (_6428 : nat) (_6429 : nat) : (term264 _6428 _6429) = (term264 _6428 _6429).
Proof. exact (eq_refl (term264 _6428 _6429)). Qed.
Lemma lem276473 (_6428 : nat) (_6429 : nat) (_6430 : nat) : (term242 _6429 _6428 _6430) = (term265 _6428 _6429 _6430).
Proof. exact (MK_COMB (@lem276472 _6428 _6429) (@lem276466 _6428 _6429 _6430)). Qed.
Lemma lem276477 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem276478 (_6428 : nat) (_6429 : nat) (_6430 : nat) : (term265 _6428 _6429 _6430) = (term266 _6428 _6429 _6430).
Proof. exact (@lem276477 (Peano.le _6428 _6430) (term39 _6428 _6429) (term39 _6429 _6430)). Qed.
Lemma lem276494 (_6428 : nat) (_6429 : nat) (_6430 : nat) : (term242 _6429 _6428 _6430) = (term266 _6428 _6429 _6430).
Proof. exact (TRANS (@lem276473 _6428 _6429 _6430) (@lem276478 _6428 _6429 _6430)). Qed.
Lemma lem276495 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem276496 (_6428 : nat) (_6429 : nat) (_6430 : nat) : (term267 _6429 _6428 _6430) = (term268 _6428 _6429 _6430).
Proof. exact (MK_COMB (@lem276495) (@lem276494 _6428 _6429 _6430)). Qed.
Lemma lem276512 (_6428 : nat) (_6429 : nat) (_6430 : nat) : (term266 _6428 _6429 _6430) = (term266 _6428 _6429 _6430).
Proof. exact (eq_refl (term266 _6428 _6429 _6430)). Qed.
Lemma lem276513 (_6428 : nat) (_6429 : nat) (_6430 : nat) : ((term242 _6429 _6428 _6430) = (term266 _6428 _6429 _6430)) = ((term266 _6428 _6429 _6430) = (term266 _6428 _6429 _6430)).
Proof. exact (MK_COMB (@lem276496 _6428 _6429 _6430) (@lem276512 _6428 _6429 _6430)). Qed.
Lemma lem276515 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem276516 (x : Prop) : (x = x) = True.
Proof. exact (@lem276515 Prop x). Qed.
Lemma lem276517 (_6428 : nat) (_6429 : nat) (_6430 : nat) : ((term266 _6428 _6429 _6430) = (term266 _6428 _6429 _6430)) = True.
Proof. exact (@lem276516 (term266 _6428 _6429 _6430)). Qed.
Lemma lem276518 (_6428 : nat) (_6429 : nat) (_6430 : nat) : ((term242 _6429 _6428 _6430) = (term266 _6428 _6429 _6430)) = True.
Proof. exact (TRANS (@lem276513 _6428 _6429 _6430) (@lem276517 _6428 _6429 _6430)). Qed.
Lemma lem276519 (_6428 : nat) (_6429 : nat) (_6430 : nat) : True = ((term242 _6429 _6428 _6430) = (term266 _6428 _6429 _6430)).
Proof. exact (SYM (@lem276518 _6428 _6429 _6430)). Qed.
Lemma lem276520 (_6428 : nat) (_6429 : nat) (_6430 : nat) : (term242 _6429 _6428 _6430) = (term266 _6428 _6429 _6430).
Proof. exact (EQ_MP (@lem276519 _6428 _6429 _6430) (@lem0)). Qed.
Lemma lem276521 (_6428 : nat) (_6429 : nat) (_6430 : nat) (h1 : term49) : term266 _6428 _6429 _6430.
Proof. exact (EQ_MP (@lem276520 _6428 _6429 _6430) (@lem276329 _6429 _6428 _6430 h1)). Qed.
Lemma lem276523 (b : Prop) (a : Prop) : (a \/ b) = (term247 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem276524 (_6429 : nat) (_6428 : nat) (_6430 : nat) : (term266 _6428 _6429 _6430) = (term269 _6429 _6428 _6430).
Proof. exact (@lem276523 (term143 _6428 _6429 _6430) (Peano.le _6428 _6430)). Qed.
Lemma lem276526 (a : Prop) (b : Prop) : (term270 a b) = (term271 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem276527 (_6428 : nat) (_6429 : nat) (_6430 : nat) : (term272 _6428 _6429 _6430) = (term273 _6428 _6429 _6430).
Proof. exact (@lem276526 (term39 _6428 _6429) (term39 _6429 _6430)). Qed.
Lemma lem276529 (a : Prop) : (term250 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem276530 (_6428 : nat) (_6429 : nat) : (term155 _6428 _6429) = (Peano.le _6428 _6429).
Proof. exact (@lem276529 (Peano.le _6428 _6429)). Qed.
Lemma lem276531 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem276532 (_6428 : nat) (_6429 : nat) : (term274 _6428 _6429) = (term275 _6428 _6429).
Proof. exact (MK_COMB (@lem276531) (@lem276530 _6428 _6429)). Qed.
Lemma lem276534 (a : Prop) : (term250 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem276535 (_6429 : nat) (_6430 : nat) : (term155 _6429 _6430) = (Peano.le _6429 _6430).
Proof. exact (@lem276534 (Peano.le _6429 _6430)). Qed.
Lemma lem276536 (_6428 : nat) (_6429 : nat) (_6430 : nat) : (term273 _6428 _6429 _6430) = (term148 _6428 _6429 _6430).
Proof. exact (MK_COMB (@lem276532 _6428 _6429) (@lem276535 _6429 _6430)). Qed.
Lemma lem276537 (_6428 : nat) (_6429 : nat) (_6430 : nat) : (term272 _6428 _6429 _6430) = (term148 _6428 _6429 _6430).
Proof. exact (TRANS (@lem276527 _6428 _6429 _6430) (@lem276536 _6428 _6429 _6430)). Qed.
Lemma lem276538 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem276539 (_6428 : nat) (_6429 : nat) (_6430 : nat) : (term276 _6428 _6429 _6430) = (term277 _6428 _6429 _6430).
Proof. exact (MK_COMB (@lem276538) (@lem276537 _6428 _6429 _6430)). Qed.
Lemma lem276540 (_6428 : nat) (_6430 : nat) : (Peano.le _6428 _6430) = (Peano.le _6428 _6430).
Proof. exact (eq_refl (Peano.le _6428 _6430)). Qed.
Lemma lem276541 (_6429 : nat) (_6428 : nat) (_6430 : nat) : (term269 _6429 _6428 _6430) = (term43 _6429 _6428 _6430).
Proof. exact (MK_COMB (@lem276539 _6428 _6429 _6430) (@lem276540 _6428 _6430)). Qed.
Lemma lem276542 (_6429 : nat) (_6428 : nat) (_6430 : nat) : (term266 _6428 _6429 _6430) = (term43 _6429 _6428 _6430).
Proof. exact (TRANS (@lem276524 _6429 _6428 _6430) (@lem276541 _6429 _6428 _6430)). Qed.
Lemma lem276544 (P : nat -> Prop) (n : nat) (i : nat) (h1 : term25) (h2 : term138 i P n) (h3 : term224 P n i) : term278 n P i.
Proof. exact (conj (@lem276402 P n i h3) (@lem276449 P n i h1 h2 h3)). Qed.
Lemma lem276546 (_6429 : nat) (_6428 : nat) (_6430 : nat) (h1 : term49) : term43 _6429 _6428 _6430.
Proof. exact (EQ_MP (@lem276542 _6429 _6428 _6430) (@lem276521 _6428 _6429 _6430 h1)). Qed.
Lemma lem276547 (P : nat -> Prop) (n : nat) (i : nat) (h1 : term49) : term279 P n i.
Proof. exact (@lem276546 (minimal P) n i h1). Qed.
Lemma lem276550 (P : nat -> Prop) (n : nat) (i : nat) (h1 : term49) (h2 : term25) (h3 : term138 i P n) (h4 : term224 P n i) : Peano.le n i.
Proof. exact (@lem276547 P n i h1 (@lem276544 P n i h2 h3 h4)). Qed.
Lemma lem276551 (P : nat -> Prop) (n : nat) (i : nat) (h1 : term49) (h2 : term25) (h3 : term138 i P n) (h4 : term224 P n i) : term280 n i.
Proof. exact (fun h0 : term39 n i => @lem276550 P n i h1 h2 h3 h4). Qed.
Lemma lem276553 (p : Prop) : (term245 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem276554 (n : nat) (i : nat) : (term280 n i) = (Peano.le n i).
Proof. exact (@lem276553 (Peano.le n i)). Qed.
Lemma lem276555 (P : nat -> Prop) (n : nat) (i : nat) (h1 : term49) (h2 : term25) (h3 : term138 i P n) (h4 : term224 P n i) : Peano.le n i.
Proof. exact (EQ_MP (@lem276554 n i) (@lem276551 P n i h1 h2 h3 h4)). Qed.
Lemma lem276558 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem276560 (n : nat) (i : nat) : (term39 n i) = (term281 n i).
Proof. exact (@lem276558 (Peano.le n i)). Qed.
Lemma lem276563 (P : nat -> Prop) (n : nat) (i : nat) (h1 : term224 P n i) : term281 n i.
Proof. exact (EQ_MP (@lem276560 n i) (@lem276355 P n i h1)). Qed.
Lemma lem276566 (P : nat -> Prop) (n : nat) (i : nat) (h1 : term49) (h2 : term25) (h3 : term138 i P n) (h4 : term224 P n i) : False.
Proof. exact (@lem276563 P n i h4 (@lem276555 P n i h1 h2 h3 h4)). Qed.
Lemma lem276567 (P : nat -> Prop) (n : nat) (i : nat) (h1 : term49) (h2 : term25) (h3 : term138 i P n) (h4 : term224 P n i) : term282.
Proof. exact (fun h0 : ~ False => @lem276566 P n i h1 h2 h3 h4). Qed.
Lemma lem276569 (p : Prop) : (term245 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem276570 : term282 = False.
Proof. exact (@lem276569 False). Qed.
Lemma lem276571 (P : nat -> Prop) (n : nat) (i : nat) (h1 : term49) (h2 : term25) (h3 : term138 i P n) (h4 : term224 P n i) : False.
Proof. exact (EQ_MP (@lem276570) (@lem276567 P n i h1 h2 h3 h4)). Qed.
Lemma lem276573 (i : nat) (P : nat -> Prop) (n : nat) (h1 : term138 i P n) : term232 P.
Proof. exact (proj1 (@lem276077 i P n h1)). Qed.
Lemma lem276574 (i : nat) (P : nat -> Prop) (n : nat) (h1 : term138 i P n) : term283 P.
Proof. exact (fun h0 : term284 P => @lem276573 i P n h1). Qed.
Lemma lem276576 (p : Prop) : (term245 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem276577 (P : nat -> Prop) : (term283 P) = (term232 P).
Proof. exact (@lem276576 (term232 P)). Qed.
Lemma lem276578 (i : nat) (P : nat -> Prop) (n : nat) (h1 : term138 i P n) : term232 P.
Proof. exact (EQ_MP (@lem276577 P) (@lem276574 i P n h1)). Qed.
Lemma lem276584 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem276585 (n : nat) (P : nat -> Prop) (_6444 : nat) : (term217 P n _6444) = (term285 n P _6444).
Proof. exact (@lem276584 (Peano.le n _6444) (term214 P _6444)). Qed.
Lemma lem276591 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem276592 (n : nat) (P : nat -> Prop) (_6444 : nat) : (term286 P n _6444) = (term287 n P _6444).
Proof. exact (MK_COMB (@lem276591) (@lem276585 n P _6444)). Qed.
Lemma lem276598 (n : nat) (P : nat -> Prop) (_6444 : nat) : (term285 n P _6444) = (term285 n P _6444).
Proof. exact (eq_refl (term285 n P _6444)). Qed.
Lemma lem276599 (n : nat) (P : nat -> Prop) (_6444 : nat) : ((term217 P n _6444) = (term285 n P _6444)) = ((term285 n P _6444) = (term285 n P _6444)).
Proof. exact (MK_COMB (@lem276592 n P _6444) (@lem276598 n P _6444)). Qed.
Lemma lem276601 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem276602 (x : Prop) : (x = x) = True.
Proof. exact (@lem276601 Prop x). Qed.
Lemma lem276603 (n : nat) (P : nat -> Prop) (_6444 : nat) : ((term285 n P _6444) = (term285 n P _6444)) = True.
Proof. exact (@lem276602 (term285 n P _6444)). Qed.
Lemma lem276604 (n : nat) (P : nat -> Prop) (_6444 : nat) : ((term217 P n _6444) = (term285 n P _6444)) = True.
Proof. exact (TRANS (@lem276599 n P _6444) (@lem276603 n P _6444)). Qed.
Lemma lem276605 (n : nat) (P : nat -> Prop) (_6444 : nat) : True = ((term217 P n _6444) = (term285 n P _6444)).
Proof. exact (SYM (@lem276604 n P _6444)). Qed.
Lemma lem276606 (n : nat) (P : nat -> Prop) (_6444 : nat) : (term217 P n _6444) = (term285 n P _6444).
Proof. exact (EQ_MP (@lem276605 n P _6444) (@lem0)). Qed.
Lemma lem276607 (_6444 : nat) (P : nat -> Prop) (n : nat) (h1 : term220 P n) : term285 n P _6444.
Proof. exact (EQ_MP (@lem276606 n P _6444) (@lem276395 _6444 P n h1)). Qed.
Lemma lem276609 (b : Prop) (a : Prop) : (a \/ b) = (term247 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem276610 (P : nat -> Prop) (n : nat) (_6444 : nat) : (term285 n P _6444) = (term288 P n _6444).
Proof. exact (@lem276609 (term214 P _6444) (Peano.le n _6444)). Qed.
Lemma lem276612 (a : Prop) : (term250 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem276613 (P : nat -> Prop) (_6444 : nat) : (term251 P _6444) = (@I (nat -> Prop) P _6444).
Proof. exact (@lem276612 (@I (nat -> Prop) P _6444)). Qed.
Lemma lem276614 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem276615 (P : nat -> Prop) (_6444 : nat) : (term252 P _6444) = (term253 P _6444).
Proof. exact (MK_COMB (@lem276614) (@lem276613 P _6444)). Qed.
Lemma lem276616 (n : nat) (_6444 : nat) : (Peano.le n _6444) = (Peano.le n _6444).
Proof. exact (eq_refl (Peano.le n _6444)). Qed.
Lemma lem276617 (P : nat -> Prop) (n : nat) (_6444 : nat) : (term288 P n _6444) = (term289 P n _6444).
Proof. exact (MK_COMB (@lem276615 P _6444) (@lem276616 n _6444)). Qed.
Lemma lem276618 (P : nat -> Prop) (n : nat) (_6444 : nat) : (term285 n P _6444) = (term289 P n _6444).
Proof. exact (TRANS (@lem276610 P n _6444) (@lem276617 P n _6444)). Qed.
Lemma lem276621 (_6444 : nat) (P : nat -> Prop) (n : nat) (h1 : term220 P n) : term289 P n _6444.
Proof. exact (EQ_MP (@lem276618 P n _6444) (@lem276607 _6444 P n h1)). Qed.
Lemma lem276622 (P : nat -> Prop) (n : nat) (h1 : term220 P n) : term290 n P.
Proof. exact (@lem276621 (minimal P) P n h1). Qed.
Lemma lem276625 (i : nat) (P : nat -> Prop) (n : nat) (h1 : term220 P n) (h2 : term138 i P n) : term12 n P.
Proof. exact (@lem276622 P n h1 (@lem276578 i P n h2)). Qed.
Lemma lem276626 (i : nat) (P : nat -> Prop) (n : nat) (h1 : term220 P n) (h2 : term138 i P n) : term244 n P.
Proof. exact (fun h0 : term243 n P => @lem276625 i P n h1 h2). Qed.
Lemma lem276628 (p : Prop) : (term245 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem276629 (n : nat) (P : nat -> Prop) : (term244 n P) = (term12 n P).
Proof. exact (@lem276628 (term12 n P)). Qed.
Lemma lem276630 (i : nat) (P : nat -> Prop) (n : nat) (h1 : term220 P n) (h2 : term138 i P n) : term12 n P.
Proof. exact (EQ_MP (@lem276629 n P) (@lem276626 i P n h1 h2)). Qed.
Lemma lem276633 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem276635 (n : nat) (P : nat -> Prop) : (term243 n P) = (term291 n P).
Proof. exact (@lem276633 (term12 n P)). Qed.
Lemma lem276638 (P : nat -> Prop) (n : nat) (h1 : term220 P n) : term291 n P.
Proof. exact (EQ_MP (@lem276635 n P) (@lem276389 P n h1)). Qed.
Lemma lem276641 (i : nat) (P : nat -> Prop) (n : nat) (h1 : term220 P n) (h2 : term138 i P n) : False.
Proof. exact (@lem276638 P n h1 (@lem276630 i P n h1 h2)). Qed.
Lemma lem276642 (i : nat) (P : nat -> Prop) (n : nat) (h1 : term220 P n) (h2 : term138 i P n) : term282.
Proof. exact (fun h0 : ~ False => @lem276641 i P n h1 h2). Qed.
Lemma lem276644 (p : Prop) : (term245 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem276645 : term282 = False.
Proof. exact (@lem276644 False). Qed.
Lemma lem276646 (i : nat) (P : nat -> Prop) (n : nat) (h1 : term220 P n) (h2 : term138 i P n) : False.
Proof. exact (EQ_MP (@lem276645) (@lem276642 i P n h1 h2)). Qed.
Lemma lem276647 (i : nat) (P : nat -> Prop) (n : nat) (h1 : term49) (h2 : term25) (h3 : term138 i P n) : False.
Proof. exact (or_elim (@lem276076 i P n h3) (fun h0 : term224 P n i => @lem276571 P n i h1 h2 h3 h0) (fun h0 : term220 P n => @lem276646 i P n h0 h3)). Qed.
Lemma lem276648 (P : nat -> Prop) (n : nat) (h1 : term49) (h2 : term25) (h3 : term18 P n) : False.
Proof. exact (ex_elim (@lem275515 P n h3) (fun i : nat => fun h0 : term140 P n i => @lem276647 i P n h1 h2 h0)). Qed.
Lemma lem276649 (P : nat -> Prop) (n : nat) (h1 : term49) (h2 : term18 P n) : term23.
Proof. exact (fun h0 : term25 => @lem276648 P n h1 h0 h2). Qed.
Lemma lem276650 : term23 = term24.
Proof. exact (@lem69 term25). Qed.
Lemma lem276651 (P : nat -> Prop) (n : nat) (h1 : term49) (h2 : term18 P n) : term24.
Proof. exact (EQ_MP (@lem276650) (@lem276649 P n h1 h2)). Qed.
Lemma lem276652 (P : nat -> Prop) (n : nat) (h1 : term18 P n) : term28.
Proof. exact (fun h0 : term49 => @lem276651 P n h0 h1). Qed.
Lemma lem276653 (P : nat -> Prop) (n : nat) : term30 P n.
Proof. exact (fun h0 : term18 P n => @lem276652 P n h0). Qed.
Lemma lem276658 (n : nat) : term34 n.
Proof. exact (fun P : nat -> Prop => @lem276653 P n). Qed.
Lemma lem276663 : term38.
Proof. exact (fun n : nat => @lem276658 n). Qed.
Lemma lem276664 : term37.
Proof. exact (EQ_MP (@lem275253) (@lem276663)). Qed.
Lemma lem276665 (n : nat) : term292 n.
Proof. exact (@lem276664 n). Qed.
Lemma lem276666 (n : nat) : (term292 n) = (term33 n).
Proof. exact (eq_refl (term292 n)). Qed.
Lemma lem276667 (n : nat) : term33 n.
Proof. exact (EQ_MP (@lem276666 n) (@lem276665 n)). Qed.
Lemma lem276668 (n : nat) (P : nat -> Prop) : term293 n P.
Proof. exact (@lem276667 n P). Qed.
Lemma lem276669 (P : nat -> Prop) (n : nat) : (term293 n P) = (term19 P n).
Proof. exact (eq_refl (term293 n P)). Qed.
Lemma lem276670 (P : nat -> Prop) (n : nat) : term19 P n.
Proof. exact (EQ_MP (@lem276669 P n) (@lem276668 n P)). Qed.
Lemma lem276672 (P : nat -> Prop) (n : nat) : term19 P n.
Proof. exact (@lem275022 P n (@lem276670 P n)). Qed.
Lemma lem276673 (P : nat -> Prop) (n : nat) (h1 : term18 P n) : term27.
Proof. exact (@lem276672 P n (@lem275007 P n h1)). Qed.
Lemma lem276674 (P : nat -> Prop) (n : nat) (h1 : term18 P n) : term23.
Proof. exact (@lem276673 P n h1 (@lem93743)). Qed.
Lemma lem276675 (P : nat -> Prop) (n : nat) (h1 : term18 P n) : False.
Proof. exact (@lem276674 P n h1 (@lem97961)). Qed.
Lemma lem276676 (P : nat -> Prop) (n : nat) (h1 : term18 P n) : (term18 P n) = False.
Proof. exact (prop_ext (fun h2 : term18 P n => @lem276675 P n h1) (fun h2 : False => @lem275007 P n h1)). Qed.
Lemma lem276677 (P : nat -> Prop) (n : nat) (h1 : term18 P n) : False.
Proof. exact (EQ_MP (@lem276676 P n h1) (@lem275007 P n h1)). Qed.
Lemma lem276678 (P : nat -> Prop) (n : nat) : term17 P n.
Proof. exact (fun h0 : term18 P n => @lem276677 P n h0). Qed.
Lemma lem276679 (P : nat -> Prop) (n : nat) : term15 P n.
Proof. exact (EQ_MP (@lem275006 P n) (@lem276678 P n)). Qed.
Lemma lem276680 (P : nat -> Prop) (n : nat) : term14 P n.
Proof. exact (EQ_MP (@lem275002 P n) (@lem276679 P n)). Qed.
Lemma lem276685 (P : nat -> Prop) : term294 P.
Proof. exact (fun n : nat => @lem276680 P n). Qed.
Lemma lem276690 : term295.
Proof. exact (fun P : nat -> Prop => @lem276685 P). Qed.
