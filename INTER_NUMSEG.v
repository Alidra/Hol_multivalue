Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTER_NUMSEG_term_abbrevs.
Require Import EXTENSION_spec.
Require Import INT_POS_spec.
Require Import IN_INTER_spec.
Require Import IN_NUMSEG_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482686_spec.
Require Import thm1482698_spec.
Require Import thm1483205_spec.
Require Import thm1483429_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988289_spec.
Require Import thm1988291_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm2318495_spec.
Require Import thm2318505_spec.
Require Import thm2318506_spec.
Require Import thm2318511_spec.
Require Import thm2318512_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841368_spec.
Require Import thm2841369_spec.
Require Import thm2841374_spec.
Require Import thm2841375_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem5436089 (m : nat) : term0 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem5436090 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem5436091 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem5436090 m) (@lem5436089 m)). Qed.
Lemma lem5436092 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem5436091 m n). Qed.
Lemma lem5436093 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem5436094 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem5436093 m n) (@lem5436092 m n)). Qed.
Lemma lem5436095 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem5436094 m n p). Qed.
Lemma lem5436096 (m : nat) (p : nat) (n : nat) : (term4 m n p) = ((term5 p m n) = (term6 m p n)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem5436098 {A : Type'} (s : A -> Prop) : term7 A s.
Proof. exact (@lem3205222 A s). Qed.
Lemma lem5436099 {A : Type'} (s : A -> Prop) : (term7 A s) = (term8 A s).
Proof. exact (eq_refl (term7 A s)). Qed.
Lemma lem5436100 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (EQ_MP (@lem5436099 A s) (@lem5436098 A s)). Qed.
Lemma lem5436101 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term9 A s t.
Proof. exact (@lem5436100 A s t). Qed.
Lemma lem5436102 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term9 A s t) = (term10 A s t).
Proof. exact (eq_refl (term9 A s t)). Qed.
Lemma lem5436103 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term10 A s t.
Proof. exact (EQ_MP (@lem5436102 A s t) (@lem5436101 A s t)). Qed.
Lemma lem5436104 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term11 A s t x.
Proof. exact (@lem5436103 A s t x). Qed.
Lemma lem5436105 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term11 A s t x) = ((term12 A x s t) = (term13 A s x t)).
Proof. exact (eq_refl (term11 A s t x)). Qed.
Lemma lem5436107 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem5436108 {A : Type'} (s : A -> Prop) : (term14 A s) = (term15 A s).
Proof. exact (eq_refl (term14 A s)). Qed.
Lemma lem5436109 {A : Type'} (s : A -> Prop) : term15 A s.
Proof. exact (EQ_MP (@lem5436108 A s) (@lem5436107 A s)). Qed.
Lemma lem5436110 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term16 A s t.
Proof. exact (@lem5436109 A s t). Qed.
Lemma lem5436111 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term16 A s t) = ((s = t) = (term17 A s t)).
Proof. exact (eq_refl (term16 A s t)). Qed.
Lemma lem5436132 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term17 A s t).
Proof. exact (EQ_MP (@lem5436111 A s t) (@lem5436110 A s t)). Qed.
Lemma lem5436133 (s : nat -> Prop) (t : nat -> Prop) : (s = t) = (term18 s t).
Proof. exact (@lem5436132 nat s t). Qed.
Lemma lem5436134 (m : nat) (p : nat) (n : nat) (q : nat) : ((term19 m n p q) = (term20 m p n q)) = (term21 m p n q).
Proof. exact (@lem5436133 (term19 m n p q) (term20 m p n q)). Qed.
Lemma lem5436144 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term12 A x s t) = (term13 A s x t).
Proof. exact (EQ_MP (@lem5436105 A s x t) (@lem5436104 A s t x)). Qed.
Lemma lem5436145 (s : nat -> Prop) (x : nat) (t : nat -> Prop) : (term22 x s t) = (term23 s x t).
Proof. exact (@lem5436144 nat s x t). Qed.
Lemma lem5436146 (m : nat) (n : nat) (x : nat) (p : nat) (q : nat) : (term24 x m n p q) = (term25 m n x p q).
Proof. exact (@lem5436145 (dotdot m n) x (dotdot p q)). Qed.
Lemma lem5436150 (m : nat) (p : nat) (n : nat) : (term5 p m n) = (term6 m p n).
Proof. exact (EQ_MP (@lem5436096 m p n) (@lem5436095 m n p)). Qed.
Lemma lem5436151 (m : nat) (x : nat) (n : nat) : (term5 x m n) = (term6 m x n).
Proof. exact (@lem5436150 m x n). Qed.
Lemma lem5436154 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5436155 (m : nat) (x : nat) (n : nat) : (term26 x m n) = (term27 m x n).
Proof. exact (MK_COMB (@lem5436154) (@lem5436151 m x n)). Qed.
Lemma lem5436157 (m : nat) (p : nat) (n : nat) : (term5 p m n) = (term6 m p n).
Proof. exact (EQ_MP (@lem5436096 m p n) (@lem5436095 m n p)). Qed.
Lemma lem5436158 (p : nat) (x : nat) (q : nat) : (term5 x p q) = (term6 p x q).
Proof. exact (@lem5436157 p x q). Qed.
Lemma lem5436161 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term25 m n x p q) = (term28 m n p x q).
Proof. exact (MK_COMB (@lem5436155 m x n) (@lem5436158 p x q)). Qed.
Lemma lem5436164 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term24 x m n p q) = (term28 m n p x q).
Proof. exact (TRANS (@lem5436146 m n x p q) (@lem5436161 m n p x q)). Qed.
Lemma lem5436165 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5436166 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term29 x m n p q) = (term30 m n p x q).
Proof. exact (MK_COMB (@lem5436165) (@lem5436164 m n p x q)). Qed.
Lemma lem5436168 (m : nat) (p : nat) (n : nat) : (term5 p m n) = (term6 m p n).
Proof. exact (EQ_MP (@lem5436096 m p n) (@lem5436095 m n p)). Qed.
Lemma lem5436169 (m : nat) (p : nat) (x : nat) (n : nat) (q : nat) : (term31 x m p n q) = (term32 m p x n q).
Proof. exact (@lem5436168 (Nat.max m p) x (Nat.min n q)). Qed.
Lemma lem5436172 (m : nat) (p : nat) (x : nat) (n : nat) (q : nat) : ((term24 x m n p q) = (term31 x m p n q)) = ((term28 m n p x q) = (term32 m p x n q)).
Proof. exact (MK_COMB (@lem5436166 m n p x q) (@lem5436169 m p x n q)). Qed.
Lemma lem5436177 (m : nat) (p : nat) (n : nat) (q : nat) : (term33 m p n q) = (term34 m p n q).
Proof. exact (fun_ext (fun x : nat => @lem5436172 m p x n q)). Qed.
Lemma lem5436178 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436179 (m : nat) (p : nat) (n : nat) (q : nat) : (term21 m p n q) = (term35 m p n q).
Proof. exact (MK_COMB (@lem5436178) (@lem5436177 m p n q)). Qed.
Lemma lem5436184 (m : nat) (p : nat) (n : nat) (q : nat) : ((term19 m n p q) = (term20 m p n q)) = (term35 m p n q).
Proof. exact (TRANS (@lem5436134 m p n q) (@lem5436179 m p n q)). Qed.
Lemma lem5436185 (m : nat) (p : nat) (n : nat) : (term36 m p n) = (term37 m p n).
Proof. exact (fun_ext (fun q : nat => @lem5436184 m p n q)). Qed.
Lemma lem5436186 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436187 (m : nat) (p : nat) (n : nat) : (term38 m p n) = (term39 m p n).
Proof. exact (MK_COMB (@lem5436186) (@lem5436185 m p n)). Qed.
Lemma lem5436192 (m : nat) (n : nat) : (term40 m n) = (term41 m n).
Proof. exact (fun_ext (fun p : nat => @lem5436187 m p n)). Qed.
Lemma lem5436193 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436194 (m : nat) (n : nat) : (term42 m n) = (term43 m n).
Proof. exact (MK_COMB (@lem5436193) (@lem5436192 m n)). Qed.
Lemma lem5436199 (m : nat) : (term44 m) = (term45 m).
Proof. exact (fun_ext (fun n : nat => @lem5436194 m n)). Qed.
Lemma lem5436200 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436201 (m : nat) : (term46 m) = (term47 m).
Proof. exact (MK_COMB (@lem5436200) (@lem5436199 m)). Qed.
Lemma lem5436206 : term48 = term49.
Proof. exact (fun_ext (fun m : nat => @lem5436201 m)). Qed.
Lemma lem5436207 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436208 : term50 = term51.
Proof. exact (MK_COMB (@lem5436207) (@lem5436206)). Qed.
Lemma lem5436213 : term51 = term50.
Proof. exact (SYM (@lem5436208)). Qed.
Lemma lem5436265 (m : nat) (p : nat) (x : nat) (n : nat) (q : nat) : ((term28 m n p x q) = (term32 m p x n q)) = ((term28 m n p x q) = (term32 m p x n q)).
Proof. exact (eq_refl ((term28 m n p x q) = (term32 m p x n q))). Qed.
Lemma lem5436266 (m : nat) (p : nat) (n : nat) (q : nat) : (term34 m p n q) = (term34 m p n q).
Proof. exact (fun_ext (fun x : nat => @lem5436265 m p x n q)). Qed.
Lemma lem5436267 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436268 (m : nat) (p : nat) (n : nat) (q : nat) : (term35 m p n q) = (term35 m p n q).
Proof. exact (MK_COMB (@lem5436267) (@lem5436266 m p n q)). Qed.
Lemma lem5436269 (m : nat) (p : nat) (n : nat) : (term37 m p n) = (term37 m p n).
Proof. exact (fun_ext (fun q : nat => @lem5436268 m p n q)). Qed.
Lemma lem5436270 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436271 (m : nat) (p : nat) (n : nat) : (term39 m p n) = (term39 m p n).
Proof. exact (MK_COMB (@lem5436270) (@lem5436269 m p n)). Qed.
Lemma lem5436272 (m : nat) (n : nat) : (term41 m n) = (term41 m n).
Proof. exact (fun_ext (fun p : nat => @lem5436271 m p n)). Qed.
Lemma lem5436273 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436274 (m : nat) (n : nat) : (term43 m n) = (term43 m n).
Proof. exact (MK_COMB (@lem5436273) (@lem5436272 m n)). Qed.
Lemma lem5436275 (m : nat) : (term45 m) = (term45 m).
Proof. exact (fun_ext (fun n : nat => @lem5436274 m n)). Qed.
Lemma lem5436276 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436277 (m : nat) : (term47 m) = (term47 m).
Proof. exact (MK_COMB (@lem5436276) (@lem5436275 m)). Qed.
Lemma lem5436278 : term49 = term49.
Proof. exact (fun_ext (fun m : nat => @lem5436277 m)). Qed.
Lemma lem5436279 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436281 : term51 = term51.
Proof. exact (MK_COMB (@lem5436279) (@lem5436278)). Qed.
Lemma lem5436290 (m : nat) (x : nat) (n : nat) : (term52 m x n) = (term53 m x n).
Proof. exact (@lem17045 (Peano.le m x) (Peano.le x n)). Qed.
Lemma lem5436302 (p : nat) (x : nat) (q : nat) : (term52 p x q) = (term53 p x q).
Proof. exact (@lem17045 (Peano.le p x) (Peano.le x q)). Qed.
Lemma lem5436306 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5436307 (m : nat) (x : nat) (n : nat) : (term54 m x n) = (term55 m x n).
Proof. exact (MK_COMB (@lem5436306) (@lem5436290 m x n)). Qed.
Lemma lem5436308 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term56 m n p x q) = (term57 m n p x q).
Proof. exact (MK_COMB (@lem5436307 m x n) (@lem5436302 p x q)). Qed.
Lemma lem5436309 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term58 m n p x q) = (term56 m n p x q).
Proof. exact (@lem17045 (term6 m x n) (term6 p x q)). Qed.
Lemma lem5436310 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term58 m n p x q) = (term57 m n p x q).
Proof. exact (TRANS (@lem5436309 m n p x q) (@lem5436308 m n p x q)). Qed.
Lemma lem5436322 (m : nat) (p : nat) (x : nat) (n : nat) (q : nat) : (term59 m p x n q) = (term60 m p x n q).
Proof. exact (@lem17045 (term61 m p x) (term62 x n q)). Qed.
Lemma lem5436325 (m : nat) (p : nat) (x : nat) (n : nat) (q : nat) : (term32 m p x n q) = (term32 m p x n q).
Proof. exact (eq_refl (term32 m p x n q)). Qed.
Lemma lem5436326 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5436327 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term63 m n p x q) = (term64 m n p x q).
Proof. exact (MK_COMB (@lem5436326) (@lem5436310 m n p x q)). Qed.
Lemma lem5436328 (m : nat) (p : nat) (x : nat) (n : nat) (q : nat) : (term65 m p x n q) = (term66 m p x n q).
Proof. exact (MK_COMB (@lem5436327 m n p x q) (@lem5436325 m p x n q)). Qed.
Lemma lem5436330 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term67 m n p x q) = (term67 m n p x q).
Proof. exact (eq_refl (term67 m n p x q)). Qed.
Lemma lem5436331 (m : nat) (p : nat) (x : nat) (n : nat) (q : nat) : (term68 m p x n q) = (term69 m p x n q).
Proof. exact (MK_COMB (@lem5436330 m n p x q) (@lem5436322 m p x n q)). Qed.
Lemma lem5436332 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5436333 (m : nat) (p : nat) (x : nat) (n : nat) (q : nat) : (term70 m p x n q) = (term71 m p x n q).
Proof. exact (MK_COMB (@lem5436332) (@lem5436331 m p x n q)). Qed.
Lemma lem5436334 (m : nat) (p : nat) (x : nat) (n : nat) (q : nat) : (term72 m p x n q) = (term73 m p x n q).
Proof. exact (MK_COMB (@lem5436333 m p x n q) (@lem5436328 m p x n q)). Qed.
Lemma lem5436335 (m : nat) (p : nat) (x : nat) (n : nat) (q : nat) : ((term28 m n p x q) = (term32 m p x n q)) = (term72 m p x n q).
Proof. exact (@lem17784 (term28 m n p x q) (term32 m p x n q)). Qed.
Lemma lem5436336 (m : nat) (p : nat) (x : nat) (n : nat) (q : nat) : ((term28 m n p x q) = (term32 m p x n q)) = (term73 m p x n q).
Proof. exact (TRANS (@lem5436335 m p x n q) (@lem5436334 m p x n q)). Qed.
Lemma lem5436337 (m : nat) (p : nat) (n : nat) (q : nat) : (term34 m p n q) = (term74 m p n q).
Proof. exact (fun_ext (fun x : nat => @lem5436336 m p x n q)). Qed.
Lemma lem5436338 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436339 (m : nat) (p : nat) (n : nat) (q : nat) : (term35 m p n q) = (term75 m p n q).
Proof. exact (MK_COMB (@lem5436338) (@lem5436337 m p n q)). Qed.
Lemma lem5436340 (m : nat) (p : nat) (n : nat) : (term37 m p n) = (term76 m p n).
Proof. exact (fun_ext (fun q : nat => @lem5436339 m p n q)). Qed.
Lemma lem5436341 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436342 (m : nat) (p : nat) (n : nat) : (term39 m p n) = (term77 m p n).
Proof. exact (MK_COMB (@lem5436341) (@lem5436340 m p n)). Qed.
Lemma lem5436343 (m : nat) (n : nat) : (term41 m n) = (term78 m n).
Proof. exact (fun_ext (fun p : nat => @lem5436342 m p n)). Qed.
Lemma lem5436344 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436345 (m : nat) (n : nat) : (term43 m n) = (term79 m n).
Proof. exact (MK_COMB (@lem5436344) (@lem5436343 m n)). Qed.
Lemma lem5436346 (m : nat) : (term45 m) = (term80 m).
Proof. exact (fun_ext (fun n : nat => @lem5436345 m n)). Qed.
Lemma lem5436347 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436348 (m : nat) : (term47 m) = (term81 m).
Proof. exact (MK_COMB (@lem5436347) (@lem5436346 m)). Qed.
Lemma lem5436349 : term49 = term82.
Proof. exact (fun_ext (fun m : nat => @lem5436348 m)). Qed.
Lemma lem5436350 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436351 : term51 = term83.
Proof. exact (MK_COMB (@lem5436350) (@lem5436349)). Qed.
Lemma lem5436352 : term51 = term83.
Proof. exact (TRANS (@lem5436281) (@lem5436351)). Qed.
Lemma lem5436353 (m : nat) (p : nat) (x : nat) (n : nat) (q : nat) : (term73 m p x n q) = (term73 m p x n q).
Proof. exact (eq_refl (term73 m p x n q)). Qed.
Lemma lem5436354 (m : nat) (p : nat) (n : nat) (q : nat) : (term74 m p n q) = (term74 m p n q).
Proof. exact (fun_ext (fun x : nat => @lem5436353 m p x n q)). Qed.
Lemma lem5436355 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436356 (m : nat) (p : nat) (n : nat) (q : nat) : (term75 m p n q) = (term75 m p n q).
Proof. exact (MK_COMB (@lem5436355) (@lem5436354 m p n q)). Qed.
Lemma lem5436357 (m : nat) (p : nat) (n : nat) : (term76 m p n) = (term76 m p n).
Proof. exact (fun_ext (fun q : nat => @lem5436356 m p n q)). Qed.
Lemma lem5436358 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436359 (m : nat) (p : nat) (n : nat) : (term77 m p n) = (term77 m p n).
Proof. exact (MK_COMB (@lem5436358) (@lem5436357 m p n)). Qed.
Lemma lem5436360 (m : nat) (n : nat) : (term78 m n) = (term78 m n).
Proof. exact (fun_ext (fun p : nat => @lem5436359 m p n)). Qed.
Lemma lem5436361 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436362 (m : nat) (n : nat) : (term79 m n) = (term79 m n).
Proof. exact (MK_COMB (@lem5436361) (@lem5436360 m n)). Qed.
Lemma lem5436363 (m : nat) : (term80 m) = (term80 m).
Proof. exact (fun_ext (fun n : nat => @lem5436362 m n)). Qed.
Lemma lem5436364 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436365 (m : nat) : (term81 m) = (term81 m).
Proof. exact (MK_COMB (@lem5436364) (@lem5436363 m)). Qed.
Lemma lem5436366 : term82 = term82.
Proof. exact (fun_ext (fun m : nat => @lem5436365 m)). Qed.
Lemma lem5436367 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436368 : term83 = term83.
Proof. exact (MK_COMB (@lem5436367) (@lem5436366)). Qed.
Lemma lem5436417 : term51 = term83.
Proof. exact (TRANS (@lem5436352) (@lem5436368)). Qed.
Lemma lem5436522 (m : nat) (p : nat) (x : nat) (n : nat) (q : nat) : (term73 m p x n q) = (term73 m p x n q).
Proof. exact (eq_refl (term73 m p x n q)). Qed.
Lemma lem5436523 (m : nat) (p : nat) (n : nat) (q : nat) : (term74 m p n q) = (term74 m p n q).
Proof. exact (fun_ext (fun x : nat => @lem5436522 m p x n q)). Qed.
Lemma lem5436524 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436525 (m : nat) (p : nat) (n : nat) (q : nat) : (term75 m p n q) = (term75 m p n q).
Proof. exact (MK_COMB (@lem5436524) (@lem5436523 m p n q)). Qed.
Lemma lem5436526 (m : nat) (p : nat) (n : nat) : (term76 m p n) = (term76 m p n).
Proof. exact (fun_ext (fun q : nat => @lem5436525 m p n q)). Qed.
Lemma lem5436527 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436528 (m : nat) (p : nat) (n : nat) : (term77 m p n) = (term77 m p n).
Proof. exact (MK_COMB (@lem5436527) (@lem5436526 m p n)). Qed.
Lemma lem5436529 (m : nat) (n : nat) : (term78 m n) = (term78 m n).
Proof. exact (fun_ext (fun p : nat => @lem5436528 m p n)). Qed.
Lemma lem5436530 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436531 (m : nat) (n : nat) : (term79 m n) = (term79 m n).
Proof. exact (MK_COMB (@lem5436530) (@lem5436529 m n)). Qed.
Lemma lem5436532 (m : nat) : (term80 m) = (term80 m).
Proof. exact (fun_ext (fun n : nat => @lem5436531 m n)). Qed.
Lemma lem5436533 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436534 (m : nat) : (term81 m) = (term81 m).
Proof. exact (MK_COMB (@lem5436533) (@lem5436532 m)). Qed.
Lemma lem5436535 : term82 = term82.
Proof. exact (fun_ext (fun m : nat => @lem5436534 m)). Qed.
Lemma lem5436536 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436537 : term83 = term83.
Proof. exact (MK_COMB (@lem5436536) (@lem5436535)). Qed.
Lemma lem5436540 : term51 = term83.
Proof. exact (TRANS (@lem5436417) (@lem5436537)). Qed.
Lemma lem5436542 (m : nat) (n : nat) : (Peano.le m n) = (term84 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5436543 (m : nat) (x : nat) : (Peano.le m x) = (term84 m x).
Proof. exact (@lem5436542 m x). Qed.
Lemma lem5436544 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5436545 (m : nat) (x : nat) : (term85 m x) = (term86 m x).
Proof. exact (MK_COMB (@lem5436544) (@lem5436543 m x)). Qed.
Lemma lem5436547 (m : nat) (n : nat) : (Peano.le m n) = (term84 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5436548 (x : nat) (n : nat) : (Peano.le x n) = (term84 x n).
Proof. exact (@lem5436547 x n). Qed.
Lemma lem5436549 (m : nat) (x : nat) (n : nat) : (term6 m x n) = (term87 m x n).
Proof. exact (MK_COMB (@lem5436545 m x) (@lem5436548 x n)). Qed.
Lemma lem5436550 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5436551 (m : nat) (x : nat) (n : nat) : (term27 m x n) = (term88 m x n).
Proof. exact (MK_COMB (@lem5436550) (@lem5436549 m x n)). Qed.
Lemma lem5436553 (m : nat) (n : nat) : (Peano.le m n) = (term84 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5436554 (p : nat) (x : nat) : (Peano.le p x) = (term84 p x).
Proof. exact (@lem5436553 p x). Qed.
Lemma lem5436555 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5436556 (p : nat) (x : nat) : (term85 p x) = (term86 p x).
Proof. exact (MK_COMB (@lem5436555) (@lem5436554 p x)). Qed.
Lemma lem5436558 (m : nat) (n : nat) : (Peano.le m n) = (term84 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5436559 (x : nat) (q : nat) : (Peano.le x q) = (term84 x q).
Proof. exact (@lem5436558 x q). Qed.
Lemma lem5436560 (p : nat) (x : nat) (q : nat) : (term6 p x q) = (term87 p x q).
Proof. exact (MK_COMB (@lem5436556 p x) (@lem5436559 x q)). Qed.
Lemma lem5436561 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term28 m n p x q) = (term89 m n p x q).
Proof. exact (MK_COMB (@lem5436551 m x n) (@lem5436560 p x q)). Qed.
Lemma lem5436562 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5436563 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term67 m n p x q) = (term90 m n p x q).
Proof. exact (MK_COMB (@lem5436562) (@lem5436561 m n p x q)). Qed.
Lemma lem5436565 (m : nat) (n : nat) : (Peano.le m n) = (term84 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5436566 (m : nat) (p : nat) (x : nat) : (term61 m p x) = (term91 m p x).
Proof. exact (@lem5436565 (Nat.max m p) x). Qed.
Lemma lem5436568 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (EQ_MP (@lem2841375 m n) (@lem2841374 m n)). Qed.
Lemma lem5436569 (m : nat) (p : nat) : (term92 m p) = (term93 m p).
Proof. exact (@lem5436568 m p). Qed.
Lemma lem5436570 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem5436571 (m : nat) (p : nat) : (term94 m p) = (term95 m p).
Proof. exact (MK_COMB (@lem5436570) (@lem5436569 m p)). Qed.
Lemma lem5436572 (x : nat) : (int_of_num x) = (int_of_num x).
Proof. exact (eq_refl (int_of_num x)). Qed.
Lemma lem5436573 (m : nat) (p : nat) (x : nat) : (term91 m p x) = (term96 m p x).
Proof. exact (MK_COMB (@lem5436571 m p) (@lem5436572 x)). Qed.
Lemma lem5436574 (m : nat) (p : nat) (x : nat) : (term61 m p x) = (term96 m p x).
Proof. exact (TRANS (@lem5436566 m p x) (@lem5436573 m p x)). Qed.
Lemma lem5436575 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5436576 (m : nat) (p : nat) (x : nat) : (term97 m p x) = (term98 m p x).
Proof. exact (MK_COMB (@lem5436575) (@lem5436574 m p x)). Qed.
Lemma lem5436577 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5436578 (m : nat) (p : nat) (x : nat) : (term99 m p x) = (term100 m p x).
Proof. exact (MK_COMB (@lem5436577) (@lem5436576 m p x)). Qed.
Lemma lem5436580 (m : nat) (n : nat) : (Peano.le m n) = (term84 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5436581 (x : nat) (n : nat) (q : nat) : (term62 x n q) = (term101 x n q).
Proof. exact (@lem5436580 x (Nat.min n q)). Qed.
Lemma lem5436583 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (EQ_MP (@lem2841369 m n) (@lem2841368 m n)). Qed.
Lemma lem5436584 (n : nat) (q : nat) : (term102 n q) = (term103 n q).
Proof. exact (@lem5436583 n q). Qed.
Lemma lem5436585 (x : nat) : (term104 x) = (term104 x).
Proof. exact (eq_refl (term104 x)). Qed.
Lemma lem5436586 (x : nat) (n : nat) (q : nat) : (term101 x n q) = (term105 x n q).
Proof. exact (MK_COMB (@lem5436585 x) (@lem5436584 n q)). Qed.
Lemma lem5436587 (x : nat) (n : nat) (q : nat) : (term62 x n q) = (term105 x n q).
Proof. exact (TRANS (@lem5436581 x n q) (@lem5436586 x n q)). Qed.
Lemma lem5436588 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5436589 (x : nat) (n : nat) (q : nat) : (term106 x n q) = (term107 x n q).
Proof. exact (MK_COMB (@lem5436588) (@lem5436587 x n q)). Qed.
Lemma lem5436590 (m : nat) (p : nat) (x : nat) (n : nat) (q : nat) : (term60 m p x n q) = (term108 m p x n q).
Proof. exact (MK_COMB (@lem5436578 m p x) (@lem5436589 x n q)). Qed.
Lemma lem5436591 (m : nat) (p : nat) (x : nat) (n : nat) (q : nat) : (term69 m p x n q) = (term109 m p x n q).
Proof. exact (MK_COMB (@lem5436563 m n p x q) (@lem5436590 m p x n q)). Qed.
Lemma lem5436592 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5436593 (m : nat) (p : nat) (x : nat) (n : nat) (q : nat) : (term71 m p x n q) = (term110 m p x n q).
Proof. exact (MK_COMB (@lem5436592) (@lem5436591 m p x n q)). Qed.
Lemma lem5436595 (m : nat) (n : nat) : (Peano.le m n) = (term84 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5436596 (m : nat) (x : nat) : (Peano.le m x) = (term84 m x).
Proof. exact (@lem5436595 m x). Qed.
Lemma lem5436597 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5436598 (m : nat) (x : nat) : (term111 m x) = (term112 m x).
Proof. exact (MK_COMB (@lem5436597) (@lem5436596 m x)). Qed.
Lemma lem5436599 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5436600 (m : nat) (x : nat) : (term113 m x) = (term114 m x).
Proof. exact (MK_COMB (@lem5436599) (@lem5436598 m x)). Qed.
Lemma lem5436602 (m : nat) (n : nat) : (Peano.le m n) = (term84 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5436603 (x : nat) (n : nat) : (Peano.le x n) = (term84 x n).
Proof. exact (@lem5436602 x n). Qed.
Lemma lem5436604 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5436605 (x : nat) (n : nat) : (term111 x n) = (term112 x n).
Proof. exact (MK_COMB (@lem5436604) (@lem5436603 x n)). Qed.
Lemma lem5436606 (m : nat) (x : nat) (n : nat) : (term53 m x n) = (term115 m x n).
Proof. exact (MK_COMB (@lem5436600 m x) (@lem5436605 x n)). Qed.
Lemma lem5436607 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5436608 (m : nat) (x : nat) (n : nat) : (term55 m x n) = (term116 m x n).
Proof. exact (MK_COMB (@lem5436607) (@lem5436606 m x n)). Qed.
Lemma lem5436610 (m : nat) (n : nat) : (Peano.le m n) = (term84 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5436611 (p : nat) (x : nat) : (Peano.le p x) = (term84 p x).
Proof. exact (@lem5436610 p x). Qed.
Lemma lem5436612 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5436613 (p : nat) (x : nat) : (term111 p x) = (term112 p x).
Proof. exact (MK_COMB (@lem5436612) (@lem5436611 p x)). Qed.
Lemma lem5436614 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5436615 (p : nat) (x : nat) : (term113 p x) = (term114 p x).
Proof. exact (MK_COMB (@lem5436614) (@lem5436613 p x)). Qed.
Lemma lem5436617 (m : nat) (n : nat) : (Peano.le m n) = (term84 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5436618 (x : nat) (q : nat) : (Peano.le x q) = (term84 x q).
Proof. exact (@lem5436617 x q). Qed.
Lemma lem5436619 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5436620 (x : nat) (q : nat) : (term111 x q) = (term112 x q).
Proof. exact (MK_COMB (@lem5436619) (@lem5436618 x q)). Qed.
Lemma lem5436621 (p : nat) (x : nat) (q : nat) : (term53 p x q) = (term115 p x q).
Proof. exact (MK_COMB (@lem5436615 p x) (@lem5436620 x q)). Qed.
Lemma lem5436622 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term57 m n p x q) = (term117 m n p x q).
Proof. exact (MK_COMB (@lem5436608 m x n) (@lem5436621 p x q)). Qed.
Lemma lem5436623 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5436624 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term64 m n p x q) = (term118 m n p x q).
Proof. exact (MK_COMB (@lem5436623) (@lem5436622 m n p x q)). Qed.
Lemma lem5436626 (m : nat) (n : nat) : (Peano.le m n) = (term84 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5436627 (m : nat) (p : nat) (x : nat) : (term61 m p x) = (term91 m p x).
Proof. exact (@lem5436626 (Nat.max m p) x). Qed.
Lemma lem5436629 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (EQ_MP (@lem2841375 m n) (@lem2841374 m n)). Qed.
Lemma lem5436630 (m : nat) (p : nat) : (term92 m p) = (term93 m p).
Proof. exact (@lem5436629 m p). Qed.
Lemma lem5436631 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem5436632 (m : nat) (p : nat) : (term94 m p) = (term95 m p).
Proof. exact (MK_COMB (@lem5436631) (@lem5436630 m p)). Qed.
Lemma lem5436633 (x : nat) : (int_of_num x) = (int_of_num x).
Proof. exact (eq_refl (int_of_num x)). Qed.
Lemma lem5436634 (m : nat) (p : nat) (x : nat) : (term91 m p x) = (term96 m p x).
Proof. exact (MK_COMB (@lem5436632 m p) (@lem5436633 x)). Qed.
Lemma lem5436635 (m : nat) (p : nat) (x : nat) : (term61 m p x) = (term96 m p x).
Proof. exact (TRANS (@lem5436627 m p x) (@lem5436634 m p x)). Qed.
Lemma lem5436636 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5436637 (m : nat) (p : nat) (x : nat) : (term119 m p x) = (term120 m p x).
Proof. exact (MK_COMB (@lem5436636) (@lem5436635 m p x)). Qed.
Lemma lem5436639 (m : nat) (n : nat) : (Peano.le m n) = (term84 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5436640 (x : nat) (n : nat) (q : nat) : (term62 x n q) = (term101 x n q).
Proof. exact (@lem5436639 x (Nat.min n q)). Qed.
Lemma lem5436642 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (EQ_MP (@lem2841369 m n) (@lem2841368 m n)). Qed.
Lemma lem5436643 (n : nat) (q : nat) : (term102 n q) = (term103 n q).
Proof. exact (@lem5436642 n q). Qed.
Lemma lem5436644 (x : nat) : (term104 x) = (term104 x).
Proof. exact (eq_refl (term104 x)). Qed.
Lemma lem5436645 (x : nat) (n : nat) (q : nat) : (term101 x n q) = (term105 x n q).
Proof. exact (MK_COMB (@lem5436644 x) (@lem5436643 n q)). Qed.
Lemma lem5436646 (x : nat) (n : nat) (q : nat) : (term62 x n q) = (term105 x n q).
Proof. exact (TRANS (@lem5436640 x n q) (@lem5436645 x n q)). Qed.
Lemma lem5436647 (m : nat) (p : nat) (x : nat) (n : nat) (q : nat) : (term32 m p x n q) = (term121 m p x n q).
Proof. exact (MK_COMB (@lem5436637 m p x) (@lem5436646 x n q)). Qed.
Lemma lem5436648 (m : nat) (p : nat) (x : nat) (n : nat) (q : nat) : (term66 m p x n q) = (term122 m p x n q).
Proof. exact (MK_COMB (@lem5436624 m n p x q) (@lem5436647 m p x n q)). Qed.
Lemma lem5436649 (m : nat) (p : nat) (x : nat) (n : nat) (q : nat) : (term73 m p x n q) = (term123 m p x n q).
Proof. exact (MK_COMB (@lem5436593 m p x n q) (@lem5436648 m p x n q)). Qed.
Lemma lem5436650 (m : nat) (p : nat) (n : nat) (q : nat) : (term74 m p n q) = (term124 m p n q).
Proof. exact (fun_ext (fun x : nat => @lem5436649 m p x n q)). Qed.
Lemma lem5436651 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436652 (m : nat) (p : nat) (n : nat) (q : nat) : (term75 m p n q) = (term125 m p n q).
Proof. exact (MK_COMB (@lem5436651) (@lem5436650 m p n q)). Qed.
Lemma lem5436653 (m : nat) (p : nat) (n : nat) : (term76 m p n) = (term126 m p n).
Proof. exact (fun_ext (fun q : nat => @lem5436652 m p n q)). Qed.
Lemma lem5436654 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436655 (m : nat) (p : nat) (n : nat) : (term77 m p n) = (term127 m p n).
Proof. exact (MK_COMB (@lem5436654) (@lem5436653 m p n)). Qed.
Lemma lem5436656 (m : nat) (n : nat) : (term78 m n) = (term128 m n).
Proof. exact (fun_ext (fun p : nat => @lem5436655 m p n)). Qed.
Lemma lem5436657 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436658 (m : nat) (n : nat) : (term79 m n) = (term129 m n).
Proof. exact (MK_COMB (@lem5436657) (@lem5436656 m n)). Qed.
Lemma lem5436659 (m : nat) : (term80 m) = (term130 m).
Proof. exact (fun_ext (fun n : nat => @lem5436658 m n)). Qed.
Lemma lem5436660 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436661 (m : nat) : (term81 m) = (term131 m).
Proof. exact (MK_COMB (@lem5436660) (@lem5436659 m)). Qed.
Lemma lem5436662 : term82 = term132.
Proof. exact (fun_ext (fun m : nat => @lem5436661 m)). Qed.
Lemma lem5436663 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5436664 : term83 = term133.
Proof. exact (MK_COMB (@lem5436663) (@lem5436662)). Qed.
Lemma lem5436665 : term51 = term133.
Proof. exact (TRANS (@lem5436540) (@lem5436664)). Qed.
Lemma lem5436666 (m : nat) : term134 m.
Proof. exact (@lem2307535 m). Qed.
Lemma lem5436667 (m : nat) : (term134 m) = (term135 m).
Proof. exact (eq_refl (term134 m)). Qed.
Lemma lem5436668 (m : nat) : term135 m.
Proof. exact (EQ_MP (@lem5436667 m) (@lem5436666 m)). Qed.
Lemma lem5436669 (n : nat) : term134 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem5436670 (n : nat) : (term134 n) = (term135 n).
Proof. exact (eq_refl (term134 n)). Qed.
Lemma lem5436671 (n : nat) : term135 n.
Proof. exact (EQ_MP (@lem5436670 n) (@lem5436669 n)). Qed.
Lemma lem5436672 (p : nat) : term134 p.
Proof. exact (@lem2307535 p). Qed.
Lemma lem5436673 (p : nat) : (term134 p) = (term135 p).
Proof. exact (eq_refl (term134 p)). Qed.
Lemma lem5436674 (p : nat) : term135 p.
Proof. exact (EQ_MP (@lem5436673 p) (@lem5436672 p)). Qed.
Lemma lem5436675 (q : nat) : term134 q.
Proof. exact (@lem2307535 q). Qed.
Lemma lem5436676 (q : nat) : (term134 q) = (term135 q).
Proof. exact (eq_refl (term134 q)). Qed.
Lemma lem5436677 (q : nat) : term135 q.
Proof. exact (EQ_MP (@lem5436676 q) (@lem5436675 q)). Qed.
Lemma lem5436678 (x : nat) : term134 x.
Proof. exact (@lem2307535 x). Qed.
Lemma lem5436679 (x : nat) : (term134 x) = (term135 x).
Proof. exact (eq_refl (term134 x)). Qed.
Lemma lem5436680 (x : nat) : term135 x.
Proof. exact (EQ_MP (@lem5436679 x) (@lem5436678 x)). Qed.
Lemma lem5436681 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term136 _70504 _70506 _70508 _70505 _70507) = (term137 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem2318604 (term137 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436730 (_70504 : int) (_70508 : int) (_70505 : int) : (term138 _70504 _70508 _70505) = (term139 _70504 _70508 _70505).
Proof. exact (@lem17045 (int_le _70504 _70508) (int_le _70508 _70505)). Qed.
Lemma lem5436737 (_70506 : int) (_70508 : int) (_70507 : int) : (term138 _70506 _70508 _70507) = (term139 _70506 _70508 _70507).
Proof. exact (@lem17045 (int_le _70506 _70508) (int_le _70508 _70507)). Qed.
Lemma lem5436738 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5436739 (_70504 : int) (_70508 : int) (_70505 : int) : (term140 _70504 _70508 _70505) = (term141 _70504 _70508 _70505).
Proof. exact (MK_COMB (@lem5436738) (@lem5436730 _70504 _70508 _70505)). Qed.
Lemma lem5436740 (_70504 : int) (_70505 : int) (_70506 : int) (_70508 : int) (_70507 : int) : (term142 _70504 _70505 _70506 _70508 _70507) = (term143 _70504 _70505 _70506 _70508 _70507).
Proof. exact (MK_COMB (@lem5436739 _70504 _70508 _70505) (@lem5436737 _70506 _70508 _70507)). Qed.
Lemma lem5436741 (_70504 : int) (_70505 : int) (_70506 : int) (_70508 : int) (_70507 : int) : (term144 _70504 _70505 _70506 _70508 _70507) = (term142 _70504 _70505 _70506 _70508 _70507).
Proof. exact (@lem17045 (term145 _70504 _70508 _70505) (term145 _70506 _70508 _70507)). Qed.
Lemma lem5436742 (_70504 : int) (_70505 : int) (_70506 : int) (_70508 : int) (_70507 : int) : (term144 _70504 _70505 _70506 _70508 _70507) = (term143 _70504 _70505 _70506 _70508 _70507).
Proof. exact (TRANS (@lem5436741 _70504 _70505 _70506 _70508 _70507) (@lem5436740 _70504 _70505 _70506 _70508 _70507)). Qed.
Lemma lem5436745 (_70504 : int) (_70506 : int) (_70508 : int) : (term146 _70504 _70506 _70508) = (term147 _70504 _70506 _70508).
Proof. exact (@lem16933 (term147 _70504 _70506 _70508)). Qed.
Lemma lem5436748 (_70508 : int) (_70505 : int) (_70507 : int) : (term148 _70508 _70505 _70507) = (term149 _70508 _70505 _70507).
Proof. exact (@lem16933 (term149 _70508 _70505 _70507)). Qed.
Lemma lem5436749 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5436750 (_70504 : int) (_70506 : int) (_70508 : int) : (term150 _70504 _70506 _70508) = (term151 _70504 _70506 _70508).
Proof. exact (MK_COMB (@lem5436749) (@lem5436745 _70504 _70506 _70508)). Qed.
Lemma lem5436751 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term152 _70504 _70506 _70508 _70505 _70507) = (term153 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5436750 _70504 _70506 _70508) (@lem5436748 _70508 _70505 _70507)). Qed.
Lemma lem5436752 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term154 _70504 _70506 _70508 _70505 _70507) = (term152 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem17160 (term155 _70504 _70506 _70508) (term156 _70508 _70505 _70507)). Qed.
Lemma lem5436753 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term154 _70504 _70506 _70508 _70505 _70507) = (term153 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5436752 _70504 _70506 _70508 _70505 _70507) (@lem5436751 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436754 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5436755 (_70504 : int) (_70505 : int) (_70506 : int) (_70508 : int) (_70507 : int) : (term157 _70504 _70505 _70506 _70508 _70507) = (term158 _70504 _70505 _70506 _70508 _70507).
Proof. exact (MK_COMB (@lem5436754) (@lem5436742 _70504 _70505 _70506 _70508 _70507)). Qed.
Lemma lem5436756 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term159 _70504 _70506 _70508 _70505 _70507) = (term160 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5436755 _70504 _70505 _70506 _70508 _70507) (@lem5436753 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436757 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term161 _70504 _70506 _70508 _70505 _70507) = (term159 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem17160 (term162 _70504 _70505 _70506 _70508 _70507) (term163 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436758 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term161 _70504 _70506 _70508 _70505 _70507) = (term160 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5436757 _70504 _70506 _70508 _70505 _70507) (@lem5436756 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436761 (_70504 : int) (_70508 : int) : (term164 _70504 _70508) = (int_le _70504 _70508).
Proof. exact (@lem16933 (int_le _70504 _70508)). Qed.
Lemma lem5436764 (_70508 : int) (_70505 : int) : (term164 _70508 _70505) = (int_le _70508 _70505).
Proof. exact (@lem16933 (int_le _70508 _70505)). Qed.
Lemma lem5436765 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5436766 (_70504 : int) (_70508 : int) : (term165 _70504 _70508) = (term166 _70504 _70508).
Proof. exact (MK_COMB (@lem5436765) (@lem5436761 _70504 _70508)). Qed.
Lemma lem5436767 (_70504 : int) (_70508 : int) (_70505 : int) : (term167 _70504 _70508 _70505) = (term145 _70504 _70508 _70505).
Proof. exact (MK_COMB (@lem5436766 _70504 _70508) (@lem5436764 _70508 _70505)). Qed.
Lemma lem5436768 (_70504 : int) (_70508 : int) (_70505 : int) : (term168 _70504 _70508 _70505) = (term167 _70504 _70508 _70505).
Proof. exact (@lem17160 (term169 _70504 _70508) (term169 _70508 _70505)). Qed.
Lemma lem5436769 (_70504 : int) (_70508 : int) (_70505 : int) : (term168 _70504 _70508 _70505) = (term145 _70504 _70508 _70505).
Proof. exact (TRANS (@lem5436768 _70504 _70508 _70505) (@lem5436767 _70504 _70508 _70505)). Qed.
Lemma lem5436772 (_70506 : int) (_70508 : int) : (term164 _70506 _70508) = (int_le _70506 _70508).
Proof. exact (@lem16933 (int_le _70506 _70508)). Qed.
Lemma lem5436775 (_70508 : int) (_70507 : int) : (term164 _70508 _70507) = (int_le _70508 _70507).
Proof. exact (@lem16933 (int_le _70508 _70507)). Qed.
Lemma lem5436776 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5436777 (_70506 : int) (_70508 : int) : (term165 _70506 _70508) = (term166 _70506 _70508).
Proof. exact (MK_COMB (@lem5436776) (@lem5436772 _70506 _70508)). Qed.
Lemma lem5436778 (_70506 : int) (_70508 : int) (_70507 : int) : (term167 _70506 _70508 _70507) = (term145 _70506 _70508 _70507).
Proof. exact (MK_COMB (@lem5436777 _70506 _70508) (@lem5436775 _70508 _70507)). Qed.
Lemma lem5436779 (_70506 : int) (_70508 : int) (_70507 : int) : (term168 _70506 _70508 _70507) = (term167 _70506 _70508 _70507).
Proof. exact (@lem17160 (term169 _70506 _70508) (term169 _70508 _70507)). Qed.
Lemma lem5436780 (_70506 : int) (_70508 : int) (_70507 : int) : (term168 _70506 _70508 _70507) = (term145 _70506 _70508 _70507).
Proof. exact (TRANS (@lem5436779 _70506 _70508 _70507) (@lem5436778 _70506 _70508 _70507)). Qed.
Lemma lem5436781 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5436782 (_70504 : int) (_70508 : int) (_70505 : int) : (term170 _70504 _70508 _70505) = (term171 _70504 _70508 _70505).
Proof. exact (MK_COMB (@lem5436781) (@lem5436769 _70504 _70508 _70505)). Qed.
Lemma lem5436783 (_70504 : int) (_70505 : int) (_70506 : int) (_70508 : int) (_70507 : int) : (term172 _70504 _70505 _70506 _70508 _70507) = (term162 _70504 _70505 _70506 _70508 _70507).
Proof. exact (MK_COMB (@lem5436782 _70504 _70508 _70505) (@lem5436780 _70506 _70508 _70507)). Qed.
Lemma lem5436784 (_70504 : int) (_70505 : int) (_70506 : int) (_70508 : int) (_70507 : int) : (term173 _70504 _70505 _70506 _70508 _70507) = (term172 _70504 _70505 _70506 _70508 _70507).
Proof. exact (@lem17160 (term139 _70504 _70508 _70505) (term139 _70506 _70508 _70507)). Qed.
Lemma lem5436785 (_70504 : int) (_70505 : int) (_70506 : int) (_70508 : int) (_70507 : int) : (term173 _70504 _70505 _70506 _70508 _70507) = (term162 _70504 _70505 _70506 _70508 _70507).
Proof. exact (TRANS (@lem5436784 _70504 _70505 _70506 _70508 _70507) (@lem5436783 _70504 _70505 _70506 _70508 _70507)). Qed.
Lemma lem5436792 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term174 _70504 _70506 _70508 _70505 _70507) = (term163 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem17045 (term147 _70504 _70506 _70508) (term149 _70508 _70505 _70507)). Qed.
Lemma lem5436793 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5436794 (_70504 : int) (_70505 : int) (_70506 : int) (_70508 : int) (_70507 : int) : (term175 _70504 _70505 _70506 _70508 _70507) = (term176 _70504 _70505 _70506 _70508 _70507).
Proof. exact (MK_COMB (@lem5436793) (@lem5436785 _70504 _70505 _70506 _70508 _70507)). Qed.
Lemma lem5436795 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term177 _70504 _70506 _70508 _70505 _70507) = (term178 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5436794 _70504 _70505 _70506 _70508 _70507) (@lem5436792 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436796 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term179 _70504 _70506 _70508 _70505 _70507) = (term177 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem17160 (term143 _70504 _70505 _70506 _70508 _70507) (term153 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436797 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term179 _70504 _70506 _70508 _70505 _70507) = (term178 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5436796 _70504 _70506 _70508 _70505 _70507) (@lem5436795 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436798 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5436799 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term180 _70504 _70506 _70508 _70505 _70507) = (term181 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5436798) (@lem5436758 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436800 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term182 _70504 _70506 _70508 _70505 _70507) = (term183 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5436799 _70504 _70506 _70508 _70505 _70507) (@lem5436797 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436801 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term184 _70504 _70506 _70508 _70505 _70507) = (term182 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem17045 (term185 _70504 _70506 _70508 _70505 _70507) (term186 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436802 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term184 _70504 _70506 _70508 _70505 _70507) = (term183 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5436801 _70504 _70506 _70508 _70505 _70507) (@lem5436800 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436804 (_70508 : int) : (term187 _70508) = (term187 _70508).
Proof. exact (eq_refl (term187 _70508)). Qed.
Lemma lem5436805 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term188 _70504 _70506 _70508 _70505 _70507) = (term189 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5436804 _70508) (@lem5436802 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436806 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term190 _70504 _70506 _70508 _70505 _70507) = (term188 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem17362 (term191 _70508) (term192 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436807 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term190 _70504 _70506 _70508 _70505 _70507) = (term189 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5436806 _70504 _70506 _70508 _70505 _70507) (@lem5436805 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436809 (_70507 : int) : (term187 _70507) = (term187 _70507).
Proof. exact (eq_refl (term187 _70507)). Qed.
Lemma lem5436810 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term193 _70504 _70506 _70508 _70505 _70507) = (term194 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5436809 _70507) (@lem5436807 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436811 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term195 _70504 _70506 _70508 _70505 _70507) = (term193 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem17362 (term191 _70507) (term196 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436812 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term195 _70504 _70506 _70508 _70505 _70507) = (term194 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5436811 _70504 _70506 _70508 _70505 _70507) (@lem5436810 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436814 (_70506 : int) : (term187 _70506) = (term187 _70506).
Proof. exact (eq_refl (term187 _70506)). Qed.
Lemma lem5436815 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term197 _70504 _70506 _70508 _70505 _70507) = (term198 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5436814 _70506) (@lem5436812 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436816 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term199 _70504 _70506 _70508 _70505 _70507) = (term197 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem17362 (term191 _70506) (term200 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436817 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term199 _70504 _70506 _70508 _70505 _70507) = (term198 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5436816 _70504 _70506 _70508 _70505 _70507) (@lem5436815 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436819 (_70505 : int) : (term187 _70505) = (term187 _70505).
Proof. exact (eq_refl (term187 _70505)). Qed.
Lemma lem5436820 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term201 _70504 _70506 _70508 _70505 _70507) = (term202 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5436819 _70505) (@lem5436817 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436821 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term203 _70504 _70506 _70508 _70505 _70507) = (term201 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem17362 (term191 _70505) (term204 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436822 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term203 _70504 _70506 _70508 _70505 _70507) = (term202 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5436821 _70504 _70506 _70508 _70505 _70507) (@lem5436820 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436824 (_70504 : int) : (term187 _70504) = (term187 _70504).
Proof. exact (eq_refl (term187 _70504)). Qed.
Lemma lem5436825 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term205 _70504 _70506 _70508 _70505 _70507) = (term206 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5436824 _70504) (@lem5436822 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436826 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term207 _70504 _70506 _70508 _70505 _70507) = (term205 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem17362 (term191 _70504) (term208 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436906 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term207 _70504 _70506 _70508 _70505 _70507) = (term206 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5436826 _70504 _70506 _70508 _70505 _70507) (@lem5436825 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5436909 (x : int) (y : int) : (int_le x y) = (term209 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5436910 (_70504 : int) : (term191 _70504) = (term210 _70504).
Proof. exact (@lem5436909 term211 _70504). Qed.
Lemma lem5436912 (n : nat) : (term212 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5436913 : term213 = term214.
Proof. exact (@lem5436912 (NUMERAL 0)). Qed.
Lemma lem5436914 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5436915 : term215 = term216.
Proof. exact (MK_COMB (@lem5436914) (@lem5436913)). Qed.
Lemma lem5436916 (_70504 : int) : (real_of_int _70504) = (real_of_int _70504).
Proof. exact (eq_refl (real_of_int _70504)). Qed.
Lemma lem5436917 (_70504 : int) : (term210 _70504) = (term217 _70504).
Proof. exact (MK_COMB (@lem5436915) (@lem5436916 _70504)). Qed.
Lemma lem5436919 (_70504 : int) : (term191 _70504) = (term217 _70504).
Proof. exact (TRANS (@lem5436910 _70504) (@lem5436917 _70504)). Qed.
Lemma lem5436922 (x : int) (y : int) : (int_le x y) = (term209 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5436923 (_70505 : int) : (term191 _70505) = (term210 _70505).
Proof. exact (@lem5436922 term211 _70505). Qed.
Lemma lem5436925 (n : nat) : (term212 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5436926 : term213 = term214.
Proof. exact (@lem5436925 (NUMERAL 0)). Qed.
Lemma lem5436927 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5436928 : term215 = term216.
Proof. exact (MK_COMB (@lem5436927) (@lem5436926)). Qed.
Lemma lem5436929 (_70505 : int) : (real_of_int _70505) = (real_of_int _70505).
Proof. exact (eq_refl (real_of_int _70505)). Qed.
Lemma lem5436930 (_70505 : int) : (term210 _70505) = (term217 _70505).
Proof. exact (MK_COMB (@lem5436928) (@lem5436929 _70505)). Qed.
Lemma lem5436932 (_70505 : int) : (term191 _70505) = (term217 _70505).
Proof. exact (TRANS (@lem5436923 _70505) (@lem5436930 _70505)). Qed.
Lemma lem5436935 (x : int) (y : int) : (int_le x y) = (term209 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5436936 (_70506 : int) : (term191 _70506) = (term210 _70506).
Proof. exact (@lem5436935 term211 _70506). Qed.
Lemma lem5436938 (n : nat) : (term212 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5436939 : term213 = term214.
Proof. exact (@lem5436938 (NUMERAL 0)). Qed.
Lemma lem5436940 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5436941 : term215 = term216.
Proof. exact (MK_COMB (@lem5436940) (@lem5436939)). Qed.
Lemma lem5436942 (_70506 : int) : (real_of_int _70506) = (real_of_int _70506).
Proof. exact (eq_refl (real_of_int _70506)). Qed.
Lemma lem5436943 (_70506 : int) : (term210 _70506) = (term217 _70506).
Proof. exact (MK_COMB (@lem5436941) (@lem5436942 _70506)). Qed.
Lemma lem5436945 (_70506 : int) : (term191 _70506) = (term217 _70506).
Proof. exact (TRANS (@lem5436936 _70506) (@lem5436943 _70506)). Qed.
Lemma lem5436948 (x : int) (y : int) : (int_le x y) = (term209 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5436949 (_70507 : int) : (term191 _70507) = (term210 _70507).
Proof. exact (@lem5436948 term211 _70507). Qed.
Lemma lem5436951 (n : nat) : (term212 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5436952 : term213 = term214.
Proof. exact (@lem5436951 (NUMERAL 0)). Qed.
Lemma lem5436953 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5436954 : term215 = term216.
Proof. exact (MK_COMB (@lem5436953) (@lem5436952)). Qed.
Lemma lem5436955 (_70507 : int) : (real_of_int _70507) = (real_of_int _70507).
Proof. exact (eq_refl (real_of_int _70507)). Qed.
Lemma lem5436956 (_70507 : int) : (term210 _70507) = (term217 _70507).
Proof. exact (MK_COMB (@lem5436954) (@lem5436955 _70507)). Qed.
Lemma lem5436958 (_70507 : int) : (term191 _70507) = (term217 _70507).
Proof. exact (TRANS (@lem5436949 _70507) (@lem5436956 _70507)). Qed.
Lemma lem5436961 (x : int) (y : int) : (int_le x y) = (term209 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5436962 (_70508 : int) : (term191 _70508) = (term210 _70508).
Proof. exact (@lem5436961 term211 _70508). Qed.
Lemma lem5436964 (n : nat) : (term212 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5436965 : term213 = term214.
Proof. exact (@lem5436964 (NUMERAL 0)). Qed.
Lemma lem5436966 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5436967 : term215 = term216.
Proof. exact (MK_COMB (@lem5436966) (@lem5436965)). Qed.
Lemma lem5436968 (_70508 : int) : (real_of_int _70508) = (real_of_int _70508).
Proof. exact (eq_refl (real_of_int _70508)). Qed.
Lemma lem5436969 (_70508 : int) : (term210 _70508) = (term217 _70508).
Proof. exact (MK_COMB (@lem5436967) (@lem5436968 _70508)). Qed.
Lemma lem5436971 (_70508 : int) : (term191 _70508) = (term217 _70508).
Proof. exact (TRANS (@lem5436962 _70508) (@lem5436969 _70508)). Qed.
Lemma lem5436973 (y : int) (x : int) : (term169 x y) = (term218 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5436974 (_70508 : int) (_70504 : int) : (term169 _70504 _70508) = (term218 _70508 _70504).
Proof. exact (@lem5436973 _70508 _70504). Qed.
Lemma lem5436976 (x : int) (y : int) : (int_le x y) = (term209 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5436977 (_70508 : int) (_70504 : int) : (term218 _70508 _70504) = (term219 _70508 _70504).
Proof. exact (@lem5436976 (term220 _70508) _70504). Qed.
Lemma lem5436979 (x : int) (y : int) : (term221 x y) = (term222 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5436980 (_70508 : int) : (term223 _70508) = (term224 _70508).
Proof. exact (@lem5436979 _70508 term225). Qed.
Lemma lem5436982 (n : nat) : (term212 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5436983 : term226 = term227.
Proof. exact (@lem5436982 term228). Qed.
Lemma lem5436984 (_70508 : int) : (term229 _70508) = (term229 _70508).
Proof. exact (eq_refl (term229 _70508)). Qed.
Lemma lem5436985 (_70508 : int) : (term224 _70508) = (term230 _70508).
Proof. exact (MK_COMB (@lem5436984 _70508) (@lem5436983)). Qed.
Lemma lem5436986 (_70508 : int) : (term223 _70508) = (term230 _70508).
Proof. exact (TRANS (@lem5436980 _70508) (@lem5436985 _70508)). Qed.
Lemma lem5436987 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5436988 (_70508 : int) : (term231 _70508) = (term232 _70508).
Proof. exact (MK_COMB (@lem5436987) (@lem5436986 _70508)). Qed.
Lemma lem5436989 (_70504 : int) : (real_of_int _70504) = (real_of_int _70504).
Proof. exact (eq_refl (real_of_int _70504)). Qed.
Lemma lem5436990 (_70508 : int) (_70504 : int) : (term219 _70508 _70504) = (term233 _70508 _70504).
Proof. exact (MK_COMB (@lem5436988 _70508) (@lem5436989 _70504)). Qed.
Lemma lem5436991 (_70508 : int) (_70504 : int) : (term218 _70508 _70504) = (term233 _70508 _70504).
Proof. exact (TRANS (@lem5436977 _70508 _70504) (@lem5436990 _70508 _70504)). Qed.
Lemma lem5436992 (_70508 : int) (_70504 : int) : (term169 _70504 _70508) = (term233 _70508 _70504).
Proof. exact (TRANS (@lem5436974 _70508 _70504) (@lem5436991 _70508 _70504)). Qed.
Lemma lem5436994 (y : int) (x : int) : (term169 x y) = (term218 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5436995 (_70505 : int) (_70508 : int) : (term169 _70508 _70505) = (term218 _70505 _70508).
Proof. exact (@lem5436994 _70505 _70508). Qed.
Lemma lem5436997 (x : int) (y : int) : (int_le x y) = (term209 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5436998 (_70505 : int) (_70508 : int) : (term218 _70505 _70508) = (term219 _70505 _70508).
Proof. exact (@lem5436997 (term220 _70505) _70508). Qed.
Lemma lem5437000 (x : int) (y : int) : (term221 x y) = (term222 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5437001 (_70505 : int) : (term223 _70505) = (term224 _70505).
Proof. exact (@lem5437000 _70505 term225). Qed.
Lemma lem5437003 (n : nat) : (term212 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5437004 : term226 = term227.
Proof. exact (@lem5437003 term228). Qed.
Lemma lem5437005 (_70505 : int) : (term229 _70505) = (term229 _70505).
Proof. exact (eq_refl (term229 _70505)). Qed.
Lemma lem5437006 (_70505 : int) : (term224 _70505) = (term230 _70505).
Proof. exact (MK_COMB (@lem5437005 _70505) (@lem5437004)). Qed.
Lemma lem5437007 (_70505 : int) : (term223 _70505) = (term230 _70505).
Proof. exact (TRANS (@lem5437001 _70505) (@lem5437006 _70505)). Qed.
Lemma lem5437008 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5437009 (_70505 : int) : (term231 _70505) = (term232 _70505).
Proof. exact (MK_COMB (@lem5437008) (@lem5437007 _70505)). Qed.
Lemma lem5437010 (_70508 : int) : (real_of_int _70508) = (real_of_int _70508).
Proof. exact (eq_refl (real_of_int _70508)). Qed.
Lemma lem5437011 (_70505 : int) (_70508 : int) : (term219 _70505 _70508) = (term233 _70505 _70508).
Proof. exact (MK_COMB (@lem5437009 _70505) (@lem5437010 _70508)). Qed.
Lemma lem5437012 (_70505 : int) (_70508 : int) : (term218 _70505 _70508) = (term233 _70505 _70508).
Proof. exact (TRANS (@lem5436998 _70505 _70508) (@lem5437011 _70505 _70508)). Qed.
Lemma lem5437013 (_70505 : int) (_70508 : int) : (term169 _70508 _70505) = (term233 _70505 _70508).
Proof. exact (TRANS (@lem5436995 _70505 _70508) (@lem5437012 _70505 _70508)). Qed.
Lemma lem5437014 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5437015 (_70508 : int) (_70504 : int) : (term234 _70504 _70508) = (term235 _70508 _70504).
Proof. exact (MK_COMB (@lem5437014) (@lem5436992 _70508 _70504)). Qed.
Lemma lem5437016 (_70504 : int) (_70505 : int) (_70508 : int) : (term139 _70504 _70508 _70505) = (term236 _70504 _70505 _70508).
Proof. exact (MK_COMB (@lem5437015 _70508 _70504) (@lem5437013 _70505 _70508)). Qed.
Lemma lem5437018 (y : int) (x : int) : (term169 x y) = (term218 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5437019 (_70508 : int) (_70506 : int) : (term169 _70506 _70508) = (term218 _70508 _70506).
Proof. exact (@lem5437018 _70508 _70506). Qed.
Lemma lem5437021 (x : int) (y : int) : (int_le x y) = (term209 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5437022 (_70508 : int) (_70506 : int) : (term218 _70508 _70506) = (term219 _70508 _70506).
Proof. exact (@lem5437021 (term220 _70508) _70506). Qed.
Lemma lem5437024 (x : int) (y : int) : (term221 x y) = (term222 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5437025 (_70508 : int) : (term223 _70508) = (term224 _70508).
Proof. exact (@lem5437024 _70508 term225). Qed.
Lemma lem5437027 (n : nat) : (term212 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5437028 : term226 = term227.
Proof. exact (@lem5437027 term228). Qed.
Lemma lem5437029 (_70508 : int) : (term229 _70508) = (term229 _70508).
Proof. exact (eq_refl (term229 _70508)). Qed.
Lemma lem5437030 (_70508 : int) : (term224 _70508) = (term230 _70508).
Proof. exact (MK_COMB (@lem5437029 _70508) (@lem5437028)). Qed.
Lemma lem5437031 (_70508 : int) : (term223 _70508) = (term230 _70508).
Proof. exact (TRANS (@lem5437025 _70508) (@lem5437030 _70508)). Qed.
Lemma lem5437032 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5437033 (_70508 : int) : (term231 _70508) = (term232 _70508).
Proof. exact (MK_COMB (@lem5437032) (@lem5437031 _70508)). Qed.
Lemma lem5437034 (_70506 : int) : (real_of_int _70506) = (real_of_int _70506).
Proof. exact (eq_refl (real_of_int _70506)). Qed.
Lemma lem5437035 (_70508 : int) (_70506 : int) : (term219 _70508 _70506) = (term233 _70508 _70506).
Proof. exact (MK_COMB (@lem5437033 _70508) (@lem5437034 _70506)). Qed.
Lemma lem5437036 (_70508 : int) (_70506 : int) : (term218 _70508 _70506) = (term233 _70508 _70506).
Proof. exact (TRANS (@lem5437022 _70508 _70506) (@lem5437035 _70508 _70506)). Qed.
Lemma lem5437037 (_70508 : int) (_70506 : int) : (term169 _70506 _70508) = (term233 _70508 _70506).
Proof. exact (TRANS (@lem5437019 _70508 _70506) (@lem5437036 _70508 _70506)). Qed.
Lemma lem5437039 (y : int) (x : int) : (term169 x y) = (term218 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5437040 (_70507 : int) (_70508 : int) : (term169 _70508 _70507) = (term218 _70507 _70508).
Proof. exact (@lem5437039 _70507 _70508). Qed.
Lemma lem5437042 (x : int) (y : int) : (int_le x y) = (term209 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5437043 (_70507 : int) (_70508 : int) : (term218 _70507 _70508) = (term219 _70507 _70508).
Proof. exact (@lem5437042 (term220 _70507) _70508). Qed.
Lemma lem5437045 (x : int) (y : int) : (term221 x y) = (term222 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5437046 (_70507 : int) : (term223 _70507) = (term224 _70507).
Proof. exact (@lem5437045 _70507 term225). Qed.
Lemma lem5437048 (n : nat) : (term212 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5437049 : term226 = term227.
Proof. exact (@lem5437048 term228). Qed.
Lemma lem5437050 (_70507 : int) : (term229 _70507) = (term229 _70507).
Proof. exact (eq_refl (term229 _70507)). Qed.
Lemma lem5437051 (_70507 : int) : (term224 _70507) = (term230 _70507).
Proof. exact (MK_COMB (@lem5437050 _70507) (@lem5437049)). Qed.
Lemma lem5437052 (_70507 : int) : (term223 _70507) = (term230 _70507).
Proof. exact (TRANS (@lem5437046 _70507) (@lem5437051 _70507)). Qed.
Lemma lem5437053 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5437054 (_70507 : int) : (term231 _70507) = (term232 _70507).
Proof. exact (MK_COMB (@lem5437053) (@lem5437052 _70507)). Qed.
Lemma lem5437055 (_70508 : int) : (real_of_int _70508) = (real_of_int _70508).
Proof. exact (eq_refl (real_of_int _70508)). Qed.
Lemma lem5437056 (_70507 : int) (_70508 : int) : (term219 _70507 _70508) = (term233 _70507 _70508).
Proof. exact (MK_COMB (@lem5437054 _70507) (@lem5437055 _70508)). Qed.
Lemma lem5437057 (_70507 : int) (_70508 : int) : (term218 _70507 _70508) = (term233 _70507 _70508).
Proof. exact (TRANS (@lem5437043 _70507 _70508) (@lem5437056 _70507 _70508)). Qed.
Lemma lem5437058 (_70507 : int) (_70508 : int) : (term169 _70508 _70507) = (term233 _70507 _70508).
Proof. exact (TRANS (@lem5437040 _70507 _70508) (@lem5437057 _70507 _70508)). Qed.
Lemma lem5437059 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5437060 (_70508 : int) (_70506 : int) : (term234 _70506 _70508) = (term235 _70508 _70506).
Proof. exact (MK_COMB (@lem5437059) (@lem5437037 _70508 _70506)). Qed.
Lemma lem5437061 (_70506 : int) (_70507 : int) (_70508 : int) : (term139 _70506 _70508 _70507) = (term236 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5437060 _70508 _70506) (@lem5437058 _70507 _70508)). Qed.
Lemma lem5437062 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5437063 (_70504 : int) (_70505 : int) (_70508 : int) : (term141 _70504 _70508 _70505) = (term237 _70504 _70505 _70508).
Proof. exact (MK_COMB (@lem5437062) (@lem5437016 _70504 _70505 _70508)). Qed.
Lemma lem5437064 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) : (term143 _70504 _70505 _70506 _70508 _70507) = (term238 _70504 _70505 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5437063 _70504 _70505 _70508) (@lem5437061 _70506 _70507 _70508)). Qed.
Lemma lem5437067 (x : int) (y : int) : (int_le x y) = (term209 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5437068 (_70504 : int) (_70506 : int) (_70508 : int) : (term147 _70504 _70506 _70508) = (term239 _70504 _70506 _70508).
Proof. exact (@lem5437067 (int_max _70504 _70506) _70508). Qed.
Lemma lem5437070 (x : int) (y : int) : (term240 x y) = (term241 x y).
Proof. exact (EQ_MP (@lem2318512 x y) (@lem2318511 x y)). Qed.
Lemma lem5437071 (_70504 : int) (_70506 : int) : (term240 _70504 _70506) = (term241 _70504 _70506).
Proof. exact (@lem5437070 _70504 _70506). Qed.
Lemma lem5437072 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5437073 (_70504 : int) (_70506 : int) : (term242 _70504 _70506) = (term243 _70504 _70506).
Proof. exact (MK_COMB (@lem5437072) (@lem5437071 _70504 _70506)). Qed.
Lemma lem5437074 (_70508 : int) : (real_of_int _70508) = (real_of_int _70508).
Proof. exact (eq_refl (real_of_int _70508)). Qed.
Lemma lem5437075 (_70504 : int) (_70506 : int) (_70508 : int) : (term239 _70504 _70506 _70508) = (term244 _70504 _70506 _70508).
Proof. exact (MK_COMB (@lem5437073 _70504 _70506) (@lem5437074 _70508)). Qed.
Lemma lem5437077 (_70504 : int) (_70506 : int) (_70508 : int) : (term147 _70504 _70506 _70508) = (term244 _70504 _70506 _70508).
Proof. exact (TRANS (@lem5437068 _70504 _70506 _70508) (@lem5437075 _70504 _70506 _70508)). Qed.
Lemma lem5437080 (x : int) (y : int) : (int_le x y) = (term209 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5437081 (_70508 : int) (_70505 : int) (_70507 : int) : (term149 _70508 _70505 _70507) = (term245 _70508 _70505 _70507).
Proof. exact (@lem5437080 _70508 (int_min _70505 _70507)). Qed.
Lemma lem5437083 (x : int) (y : int) : (term246 x y) = (term247 x y).
Proof. exact (EQ_MP (@lem2318506 x y) (@lem2318505 x y)). Qed.
Lemma lem5437084 (_70505 : int) (_70507 : int) : (term246 _70505 _70507) = (term247 _70505 _70507).
Proof. exact (@lem5437083 _70505 _70507). Qed.
Lemma lem5437085 (_70508 : int) : (term248 _70508) = (term248 _70508).
Proof. exact (eq_refl (term248 _70508)). Qed.
Lemma lem5437086 (_70508 : int) (_70505 : int) (_70507 : int) : (term245 _70508 _70505 _70507) = (term249 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5437085 _70508) (@lem5437084 _70505 _70507)). Qed.
Lemma lem5437088 (_70508 : int) (_70505 : int) (_70507 : int) : (term149 _70508 _70505 _70507) = (term249 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5437081 _70508 _70505 _70507) (@lem5437086 _70508 _70505 _70507)). Qed.
Lemma lem5437089 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5437090 (_70504 : int) (_70506 : int) (_70508 : int) : (term151 _70504 _70506 _70508) = (term250 _70504 _70506 _70508).
Proof. exact (MK_COMB (@lem5437089) (@lem5437077 _70504 _70506 _70508)). Qed.
Lemma lem5437091 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term153 _70504 _70506 _70508 _70505 _70507) = (term251 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5437090 _70504 _70506 _70508) (@lem5437088 _70508 _70505 _70507)). Qed.
Lemma lem5437092 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5437093 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) : (term158 _70504 _70505 _70506 _70508 _70507) = (term252 _70504 _70505 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5437092) (@lem5437064 _70504 _70505 _70506 _70507 _70508)). Qed.
Lemma lem5437094 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term160 _70504 _70506 _70508 _70505 _70507) = (term253 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5437093 _70504 _70505 _70506 _70507 _70508) (@lem5437091 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5437097 (x : int) (y : int) : (int_le x y) = (term209 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5437099 (_70504 : int) (_70508 : int) : (int_le _70504 _70508) = (term209 _70504 _70508).
Proof. exact (@lem5437097 _70504 _70508). Qed.
Lemma lem5437102 (x : int) (y : int) : (int_le x y) = (term209 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5437104 (_70508 : int) (_70505 : int) : (int_le _70508 _70505) = (term209 _70508 _70505).
Proof. exact (@lem5437102 _70508 _70505). Qed.
Lemma lem5437105 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5437106 (_70504 : int) (_70508 : int) : (term166 _70504 _70508) = (term254 _70504 _70508).
Proof. exact (MK_COMB (@lem5437105) (@lem5437099 _70504 _70508)). Qed.
Lemma lem5437107 (_70504 : int) (_70508 : int) (_70505 : int) : (term145 _70504 _70508 _70505) = (term255 _70504 _70508 _70505).
Proof. exact (MK_COMB (@lem5437106 _70504 _70508) (@lem5437104 _70508 _70505)). Qed.
Lemma lem5437110 (x : int) (y : int) : (int_le x y) = (term209 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5437112 (_70506 : int) (_70508 : int) : (int_le _70506 _70508) = (term209 _70506 _70508).
Proof. exact (@lem5437110 _70506 _70508). Qed.
Lemma lem5437115 (x : int) (y : int) : (int_le x y) = (term209 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5437117 (_70508 : int) (_70507 : int) : (int_le _70508 _70507) = (term209 _70508 _70507).
Proof. exact (@lem5437115 _70508 _70507). Qed.
Lemma lem5437118 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5437119 (_70506 : int) (_70508 : int) : (term166 _70506 _70508) = (term254 _70506 _70508).
Proof. exact (MK_COMB (@lem5437118) (@lem5437112 _70506 _70508)). Qed.
Lemma lem5437120 (_70506 : int) (_70508 : int) (_70507 : int) : (term145 _70506 _70508 _70507) = (term255 _70506 _70508 _70507).
Proof. exact (MK_COMB (@lem5437119 _70506 _70508) (@lem5437117 _70508 _70507)). Qed.
Lemma lem5437121 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5437122 (_70504 : int) (_70508 : int) (_70505 : int) : (term171 _70504 _70508 _70505) = (term256 _70504 _70508 _70505).
Proof. exact (MK_COMB (@lem5437121) (@lem5437107 _70504 _70508 _70505)). Qed.
Lemma lem5437123 (_70504 : int) (_70505 : int) (_70506 : int) (_70508 : int) (_70507 : int) : (term162 _70504 _70505 _70506 _70508 _70507) = (term257 _70504 _70505 _70506 _70508 _70507).
Proof. exact (MK_COMB (@lem5437122 _70504 _70508 _70505) (@lem5437120 _70506 _70508 _70507)). Qed.
Lemma lem5437125 (y : int) (x : int) : (term169 x y) = (term218 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5437126 (_70508 : int) (_70504 : int) (_70506 : int) : (term155 _70504 _70506 _70508) = (term258 _70508 _70504 _70506).
Proof. exact (@lem5437125 _70508 (int_max _70504 _70506)). Qed.
Lemma lem5437128 (x : int) (y : int) : (int_le x y) = (term209 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5437129 (_70508 : int) (_70504 : int) (_70506 : int) : (term258 _70508 _70504 _70506) = (term259 _70508 _70504 _70506).
Proof. exact (@lem5437128 (term220 _70508) (int_max _70504 _70506)). Qed.
Lemma lem5437131 (x : int) (y : int) : (term221 x y) = (term222 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5437132 (_70508 : int) : (term223 _70508) = (term224 _70508).
Proof. exact (@lem5437131 _70508 term225). Qed.
Lemma lem5437134 (n : nat) : (term212 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5437135 : term226 = term227.
Proof. exact (@lem5437134 term228). Qed.
Lemma lem5437136 (_70508 : int) : (term229 _70508) = (term229 _70508).
Proof. exact (eq_refl (term229 _70508)). Qed.
Lemma lem5437137 (_70508 : int) : (term224 _70508) = (term230 _70508).
Proof. exact (MK_COMB (@lem5437136 _70508) (@lem5437135)). Qed.
Lemma lem5437138 (_70508 : int) : (term223 _70508) = (term230 _70508).
Proof. exact (TRANS (@lem5437132 _70508) (@lem5437137 _70508)). Qed.
Lemma lem5437139 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5437140 (_70508 : int) : (term231 _70508) = (term232 _70508).
Proof. exact (MK_COMB (@lem5437139) (@lem5437138 _70508)). Qed.
Lemma lem5437142 (x : int) (y : int) : (term240 x y) = (term241 x y).
Proof. exact (EQ_MP (@lem2318512 x y) (@lem2318511 x y)). Qed.
Lemma lem5437143 (_70504 : int) (_70506 : int) : (term240 _70504 _70506) = (term241 _70504 _70506).
Proof. exact (@lem5437142 _70504 _70506). Qed.
Lemma lem5437144 (_70508 : int) (_70504 : int) (_70506 : int) : (term259 _70508 _70504 _70506) = (term260 _70508 _70504 _70506).
Proof. exact (MK_COMB (@lem5437140 _70508) (@lem5437143 _70504 _70506)). Qed.
Lemma lem5437145 (_70508 : int) (_70504 : int) (_70506 : int) : (term258 _70508 _70504 _70506) = (term260 _70508 _70504 _70506).
Proof. exact (TRANS (@lem5437129 _70508 _70504 _70506) (@lem5437144 _70508 _70504 _70506)). Qed.
Lemma lem5437146 (_70508 : int) (_70504 : int) (_70506 : int) : (term155 _70504 _70506 _70508) = (term260 _70508 _70504 _70506).
Proof. exact (TRANS (@lem5437126 _70508 _70504 _70506) (@lem5437145 _70508 _70504 _70506)). Qed.
Lemma lem5437148 (y : int) (x : int) : (term169 x y) = (term218 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5437149 (_70505 : int) (_70507 : int) (_70508 : int) : (term156 _70508 _70505 _70507) = (term261 _70505 _70507 _70508).
Proof. exact (@lem5437148 (int_min _70505 _70507) _70508). Qed.
Lemma lem5437151 (x : int) (y : int) : (int_le x y) = (term209 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5437152 (_70505 : int) (_70507 : int) (_70508 : int) : (term261 _70505 _70507 _70508) = (term262 _70505 _70507 _70508).
Proof. exact (@lem5437151 (term263 _70505 _70507) _70508). Qed.
Lemma lem5437154 (x : int) (y : int) : (term221 x y) = (term222 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5437155 (_70505 : int) (_70507 : int) : (term264 _70505 _70507) = (term265 _70505 _70507).
Proof. exact (@lem5437154 (int_min _70505 _70507) term225). Qed.
Lemma lem5437157 (x : int) (y : int) : (term246 x y) = (term247 x y).
Proof. exact (EQ_MP (@lem2318506 x y) (@lem2318505 x y)). Qed.
Lemma lem5437158 (_70505 : int) (_70507 : int) : (term246 _70505 _70507) = (term247 _70505 _70507).
Proof. exact (@lem5437157 _70505 _70507). Qed.
Lemma lem5437159 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5437160 (_70505 : int) (_70507 : int) : (term266 _70505 _70507) = (term267 _70505 _70507).
Proof. exact (MK_COMB (@lem5437159) (@lem5437158 _70505 _70507)). Qed.
Lemma lem5437162 (n : nat) : (term212 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5437163 : term226 = term227.
Proof. exact (@lem5437162 term228). Qed.
Lemma lem5437164 (_70505 : int) (_70507 : int) : (term265 _70505 _70507) = (term268 _70505 _70507).
Proof. exact (MK_COMB (@lem5437160 _70505 _70507) (@lem5437163)). Qed.
Lemma lem5437165 (_70505 : int) (_70507 : int) : (term264 _70505 _70507) = (term268 _70505 _70507).
Proof. exact (TRANS (@lem5437155 _70505 _70507) (@lem5437164 _70505 _70507)). Qed.
Lemma lem5437166 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5437167 (_70505 : int) (_70507 : int) : (term269 _70505 _70507) = (term270 _70505 _70507).
Proof. exact (MK_COMB (@lem5437166) (@lem5437165 _70505 _70507)). Qed.
Lemma lem5437168 (_70508 : int) : (real_of_int _70508) = (real_of_int _70508).
Proof. exact (eq_refl (real_of_int _70508)). Qed.
Lemma lem5437169 (_70505 : int) (_70507 : int) (_70508 : int) : (term262 _70505 _70507 _70508) = (term271 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5437167 _70505 _70507) (@lem5437168 _70508)). Qed.
Lemma lem5437170 (_70505 : int) (_70507 : int) (_70508 : int) : (term261 _70505 _70507 _70508) = (term271 _70505 _70507 _70508).
Proof. exact (TRANS (@lem5437152 _70505 _70507 _70508) (@lem5437169 _70505 _70507 _70508)). Qed.
Lemma lem5437171 (_70505 : int) (_70507 : int) (_70508 : int) : (term156 _70508 _70505 _70507) = (term271 _70505 _70507 _70508).
Proof. exact (TRANS (@lem5437149 _70505 _70507 _70508) (@lem5437170 _70505 _70507 _70508)). Qed.
Lemma lem5437172 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5437173 (_70508 : int) (_70504 : int) (_70506 : int) : (term272 _70504 _70506 _70508) = (term273 _70508 _70504 _70506).
Proof. exact (MK_COMB (@lem5437172) (@lem5437146 _70508 _70504 _70506)). Qed.
Lemma lem5437174 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term163 _70504 _70506 _70508 _70505 _70507) = (term274 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5437173 _70508 _70504 _70506) (@lem5437171 _70505 _70507 _70508)). Qed.
Lemma lem5437175 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5437176 (_70504 : int) (_70505 : int) (_70506 : int) (_70508 : int) (_70507 : int) : (term176 _70504 _70505 _70506 _70508 _70507) = (term275 _70504 _70505 _70506 _70508 _70507).
Proof. exact (MK_COMB (@lem5437175) (@lem5437123 _70504 _70505 _70506 _70508 _70507)). Qed.
Lemma lem5437177 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term178 _70504 _70506 _70508 _70505 _70507) = (term276 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5437176 _70504 _70505 _70506 _70508 _70507) (@lem5437174 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5437178 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5437179 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term181 _70504 _70506 _70508 _70505 _70507) = (term277 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5437178) (@lem5437094 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5437180 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term183 _70504 _70506 _70508 _70505 _70507) = (term278 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5437179 _70504 _70506 _70508 _70505 _70507) (@lem5437177 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5437181 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5437182 (_70508 : int) : (term187 _70508) = (term279 _70508).
Proof. exact (MK_COMB (@lem5437181) (@lem5436971 _70508)). Qed.
Lemma lem5437183 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term189 _70504 _70506 _70508 _70505 _70507) = (term280 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5437182 _70508) (@lem5437180 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5437184 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5437185 (_70507 : int) : (term187 _70507) = (term279 _70507).
Proof. exact (MK_COMB (@lem5437184) (@lem5436958 _70507)). Qed.
Lemma lem5437186 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term194 _70504 _70506 _70508 _70505 _70507) = (term281 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5437185 _70507) (@lem5437183 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5437187 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5437188 (_70506 : int) : (term187 _70506) = (term279 _70506).
Proof. exact (MK_COMB (@lem5437187) (@lem5436945 _70506)). Qed.
Lemma lem5437189 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term198 _70504 _70506 _70508 _70505 _70507) = (term282 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5437188 _70506) (@lem5437186 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5437190 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5437191 (_70505 : int) : (term187 _70505) = (term279 _70505).
Proof. exact (MK_COMB (@lem5437190) (@lem5436932 _70505)). Qed.
Lemma lem5437192 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term202 _70504 _70506 _70508 _70505 _70507) = (term283 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5437191 _70505) (@lem5437189 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5437193 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5437194 (_70504 : int) : (term187 _70504) = (term279 _70504).
Proof. exact (MK_COMB (@lem5437193) (@lem5436919 _70504)). Qed.
Lemma lem5437195 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term206 _70504 _70506 _70508 _70505 _70507) = (term284 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5437194 _70504) (@lem5437192 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5437196 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term207 _70504 _70506 _70508 _70505 _70507) = (term284 _70504 _70506 _70505 _70507 _70508).
Proof. exact (TRANS (@lem5436906 _70504 _70506 _70508 _70505 _70507) (@lem5437195 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5437200 (t : Prop) : (term285 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5437366 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term286 _70504 _70506 _70505 _70507 _70508) = (term284 _70504 _70506 _70505 _70507 _70508).
Proof. exact (@lem5437200 (term284 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5437367 (_70504 : int) : (term217 _70504) = (term287 _70504).
Proof. exact (@lem1988287 (real_of_int _70504) term214). Qed.
Lemma lem5437373 (_70504 : int) : (term288 _70504) = (term289 _70504).
Proof. exact (@lem1982792 (real_of_int _70504) term214). Qed.
Lemma lem5437375 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5437376 : term214 = term291.
Proof. exact (@lem5437375 (NUMERAL 0)). Qed.
Lemma lem5437378 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5437379 : term294 = term295.
Proof. exact (@lem5437378 term228). Qed.
Lemma lem5437380 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5437381 : term296 = term297.
Proof. exact (MK_COMB (@lem5437380) (@lem5437379)). Qed.
Lemma lem5437382 : term298 = term299.
Proof. exact (MK_COMB (@lem5437381) (@lem5437376)). Qed.
Lemma lem5437383 : term299 = term300.
Proof. exact (@lem1981613 term294 term214 term227 term227). Qed.
Lemma lem5437385 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5437386 : term303 = term304.
Proof. exact (@lem5437385 term228 term228). Qed.
Lemma lem5437387 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5437388 : term306 = term228.
Proof. exact (EQ_MP (@lem5437387) (@lem940073)). Qed.
Lemma lem5437389 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5437390 : term304 = term227.
Proof. exact (MK_COMB (@lem5437389) (@lem5437388)). Qed.
Lemma lem5437391 : term303 = term227.
Proof. exact (TRANS (@lem5437386) (@lem5437390)). Qed.
Lemma lem5437393 (x : nat) : (term307 x) = term214.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5437394 : term298 = term214.
Proof. exact (@lem5437393 term228). Qed.
Lemma lem5437395 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5437396 : term308 = term309.
Proof. exact (MK_COMB (@lem5437395) (@lem5437394)). Qed.
Lemma lem5437397 : term300 = term291.
Proof. exact (MK_COMB (@lem5437396) (@lem5437391)). Qed.
Lemma lem5437398 : term299 = term291.
Proof. exact (TRANS (@lem5437383) (@lem5437397)). Qed.
Lemma lem5437399 : term298 = term291.
Proof. exact (TRANS (@lem5437382) (@lem5437398)). Qed.
Lemma lem5437401 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5437402 : term291 = term214.
Proof. exact (@lem5437401 term214). Qed.
Lemma lem5437403 : term298 = term214.
Proof. exact (TRANS (@lem5437399) (@lem5437402)). Qed.
Lemma lem5437404 (_70504 : int) : (term229 _70504) = (term229 _70504).
Proof. exact (eq_refl (term229 _70504)). Qed.
Lemma lem5437405 (_70504 : int) : (term289 _70504) = (term311 _70504).
Proof. exact (MK_COMB (@lem5437404 _70504) (@lem5437403)). Qed.
Lemma lem5437406 (_70504 : int) : (term311 _70504) = (real_of_int _70504).
Proof. exact (@lem1982723 (real_of_int _70504)). Qed.
Lemma lem5437407 (_70504 : int) : (term289 _70504) = (real_of_int _70504).
Proof. exact (TRANS (@lem5437405 _70504) (@lem5437406 _70504)). Qed.
Lemma lem5437409 (_70504 : int) : (term288 _70504) = (real_of_int _70504).
Proof. exact (TRANS (@lem5437373 _70504) (@lem5437407 _70504)). Qed.
Lemma lem5437410 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5437411 (_70504 : int) : (term312 _70504) = (term313 _70504).
Proof. exact (MK_COMB (@lem5437410) (@lem5437409 _70504)). Qed.
Lemma lem5437412 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5437413 (_70504 : int) : (term287 _70504) = (term314 _70504).
Proof. exact (MK_COMB (@lem5437411 _70504) (@lem5437412)). Qed.
Lemma lem5437414 (_70504 : int) : (term217 _70504) = (term314 _70504).
Proof. exact (TRANS (@lem5437367 _70504) (@lem5437413 _70504)). Qed.
Lemma lem5437415 (_70505 : int) : (term217 _70505) = (term287 _70505).
Proof. exact (@lem1988287 (real_of_int _70505) term214). Qed.
Lemma lem5437421 (_70505 : int) : (term288 _70505) = (term289 _70505).
Proof. exact (@lem1982792 (real_of_int _70505) term214). Qed.
Lemma lem5437423 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5437424 : term214 = term291.
Proof. exact (@lem5437423 (NUMERAL 0)). Qed.
Lemma lem5437426 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5437427 : term294 = term295.
Proof. exact (@lem5437426 term228). Qed.
Lemma lem5437428 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5437429 : term296 = term297.
Proof. exact (MK_COMB (@lem5437428) (@lem5437427)). Qed.
Lemma lem5437430 : term298 = term299.
Proof. exact (MK_COMB (@lem5437429) (@lem5437424)). Qed.
Lemma lem5437431 : term299 = term300.
Proof. exact (@lem1981613 term294 term214 term227 term227). Qed.
Lemma lem5437433 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5437434 : term303 = term304.
Proof. exact (@lem5437433 term228 term228). Qed.
Lemma lem5437435 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5437436 : term306 = term228.
Proof. exact (EQ_MP (@lem5437435) (@lem940073)). Qed.
Lemma lem5437437 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5437438 : term304 = term227.
Proof. exact (MK_COMB (@lem5437437) (@lem5437436)). Qed.
Lemma lem5437439 : term303 = term227.
Proof. exact (TRANS (@lem5437434) (@lem5437438)). Qed.
Lemma lem5437441 (x : nat) : (term307 x) = term214.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5437442 : term298 = term214.
Proof. exact (@lem5437441 term228). Qed.
Lemma lem5437443 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5437444 : term308 = term309.
Proof. exact (MK_COMB (@lem5437443) (@lem5437442)). Qed.
Lemma lem5437445 : term300 = term291.
Proof. exact (MK_COMB (@lem5437444) (@lem5437439)). Qed.
Lemma lem5437446 : term299 = term291.
Proof. exact (TRANS (@lem5437431) (@lem5437445)). Qed.
Lemma lem5437447 : term298 = term291.
Proof. exact (TRANS (@lem5437430) (@lem5437446)). Qed.
Lemma lem5437449 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5437450 : term291 = term214.
Proof. exact (@lem5437449 term214). Qed.
Lemma lem5437451 : term298 = term214.
Proof. exact (TRANS (@lem5437447) (@lem5437450)). Qed.
Lemma lem5437452 (_70505 : int) : (term229 _70505) = (term229 _70505).
Proof. exact (eq_refl (term229 _70505)). Qed.
Lemma lem5437453 (_70505 : int) : (term289 _70505) = (term311 _70505).
Proof. exact (MK_COMB (@lem5437452 _70505) (@lem5437451)). Qed.
Lemma lem5437454 (_70505 : int) : (term311 _70505) = (real_of_int _70505).
Proof. exact (@lem1982723 (real_of_int _70505)). Qed.
Lemma lem5437455 (_70505 : int) : (term289 _70505) = (real_of_int _70505).
Proof. exact (TRANS (@lem5437453 _70505) (@lem5437454 _70505)). Qed.
Lemma lem5437457 (_70505 : int) : (term288 _70505) = (real_of_int _70505).
Proof. exact (TRANS (@lem5437421 _70505) (@lem5437455 _70505)). Qed.
Lemma lem5437458 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5437459 (_70505 : int) : (term312 _70505) = (term313 _70505).
Proof. exact (MK_COMB (@lem5437458) (@lem5437457 _70505)). Qed.
Lemma lem5437460 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5437461 (_70505 : int) : (term287 _70505) = (term314 _70505).
Proof. exact (MK_COMB (@lem5437459 _70505) (@lem5437460)). Qed.
Lemma lem5437462 (_70505 : int) : (term217 _70505) = (term314 _70505).
Proof. exact (TRANS (@lem5437415 _70505) (@lem5437461 _70505)). Qed.
Lemma lem5437463 (_70506 : int) : (term217 _70506) = (term287 _70506).
Proof. exact (@lem1988287 (real_of_int _70506) term214). Qed.
Lemma lem5437469 (_70506 : int) : (term288 _70506) = (term289 _70506).
Proof. exact (@lem1982792 (real_of_int _70506) term214). Qed.
Lemma lem5437471 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5437472 : term214 = term291.
Proof. exact (@lem5437471 (NUMERAL 0)). Qed.
Lemma lem5437474 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5437475 : term294 = term295.
Proof. exact (@lem5437474 term228). Qed.
Lemma lem5437476 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5437477 : term296 = term297.
Proof. exact (MK_COMB (@lem5437476) (@lem5437475)). Qed.
Lemma lem5437478 : term298 = term299.
Proof. exact (MK_COMB (@lem5437477) (@lem5437472)). Qed.
Lemma lem5437479 : term299 = term300.
Proof. exact (@lem1981613 term294 term214 term227 term227). Qed.
Lemma lem5437481 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5437482 : term303 = term304.
Proof. exact (@lem5437481 term228 term228). Qed.
Lemma lem5437483 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5437484 : term306 = term228.
Proof. exact (EQ_MP (@lem5437483) (@lem940073)). Qed.
Lemma lem5437485 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5437486 : term304 = term227.
Proof. exact (MK_COMB (@lem5437485) (@lem5437484)). Qed.
Lemma lem5437487 : term303 = term227.
Proof. exact (TRANS (@lem5437482) (@lem5437486)). Qed.
Lemma lem5437489 (x : nat) : (term307 x) = term214.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5437490 : term298 = term214.
Proof. exact (@lem5437489 term228). Qed.
Lemma lem5437491 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5437492 : term308 = term309.
Proof. exact (MK_COMB (@lem5437491) (@lem5437490)). Qed.
Lemma lem5437493 : term300 = term291.
Proof. exact (MK_COMB (@lem5437492) (@lem5437487)). Qed.
Lemma lem5437494 : term299 = term291.
Proof. exact (TRANS (@lem5437479) (@lem5437493)). Qed.
Lemma lem5437495 : term298 = term291.
Proof. exact (TRANS (@lem5437478) (@lem5437494)). Qed.
Lemma lem5437497 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5437498 : term291 = term214.
Proof. exact (@lem5437497 term214). Qed.
Lemma lem5437499 : term298 = term214.
Proof. exact (TRANS (@lem5437495) (@lem5437498)). Qed.
Lemma lem5437500 (_70506 : int) : (term229 _70506) = (term229 _70506).
Proof. exact (eq_refl (term229 _70506)). Qed.
Lemma lem5437501 (_70506 : int) : (term289 _70506) = (term311 _70506).
Proof. exact (MK_COMB (@lem5437500 _70506) (@lem5437499)). Qed.
Lemma lem5437502 (_70506 : int) : (term311 _70506) = (real_of_int _70506).
Proof. exact (@lem1982723 (real_of_int _70506)). Qed.
Lemma lem5437503 (_70506 : int) : (term289 _70506) = (real_of_int _70506).
Proof. exact (TRANS (@lem5437501 _70506) (@lem5437502 _70506)). Qed.
Lemma lem5437505 (_70506 : int) : (term288 _70506) = (real_of_int _70506).
Proof. exact (TRANS (@lem5437469 _70506) (@lem5437503 _70506)). Qed.
Lemma lem5437506 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5437507 (_70506 : int) : (term312 _70506) = (term313 _70506).
Proof. exact (MK_COMB (@lem5437506) (@lem5437505 _70506)). Qed.
Lemma lem5437508 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5437509 (_70506 : int) : (term287 _70506) = (term314 _70506).
Proof. exact (MK_COMB (@lem5437507 _70506) (@lem5437508)). Qed.
Lemma lem5437510 (_70506 : int) : (term217 _70506) = (term314 _70506).
Proof. exact (TRANS (@lem5437463 _70506) (@lem5437509 _70506)). Qed.
Lemma lem5437511 (_70507 : int) : (term217 _70507) = (term287 _70507).
Proof. exact (@lem1988287 (real_of_int _70507) term214). Qed.
Lemma lem5437517 (_70507 : int) : (term288 _70507) = (term289 _70507).
Proof. exact (@lem1982792 (real_of_int _70507) term214). Qed.
Lemma lem5437519 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5437520 : term214 = term291.
Proof. exact (@lem5437519 (NUMERAL 0)). Qed.
Lemma lem5437522 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5437523 : term294 = term295.
Proof. exact (@lem5437522 term228). Qed.
Lemma lem5437524 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5437525 : term296 = term297.
Proof. exact (MK_COMB (@lem5437524) (@lem5437523)). Qed.
Lemma lem5437526 : term298 = term299.
Proof. exact (MK_COMB (@lem5437525) (@lem5437520)). Qed.
Lemma lem5437527 : term299 = term300.
Proof. exact (@lem1981613 term294 term214 term227 term227). Qed.
Lemma lem5437529 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5437530 : term303 = term304.
Proof. exact (@lem5437529 term228 term228). Qed.
Lemma lem5437531 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5437532 : term306 = term228.
Proof. exact (EQ_MP (@lem5437531) (@lem940073)). Qed.
Lemma lem5437533 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5437534 : term304 = term227.
Proof. exact (MK_COMB (@lem5437533) (@lem5437532)). Qed.
Lemma lem5437535 : term303 = term227.
Proof. exact (TRANS (@lem5437530) (@lem5437534)). Qed.
Lemma lem5437537 (x : nat) : (term307 x) = term214.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5437538 : term298 = term214.
Proof. exact (@lem5437537 term228). Qed.
Lemma lem5437539 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5437540 : term308 = term309.
Proof. exact (MK_COMB (@lem5437539) (@lem5437538)). Qed.
Lemma lem5437541 : term300 = term291.
Proof. exact (MK_COMB (@lem5437540) (@lem5437535)). Qed.
Lemma lem5437542 : term299 = term291.
Proof. exact (TRANS (@lem5437527) (@lem5437541)). Qed.
Lemma lem5437543 : term298 = term291.
Proof. exact (TRANS (@lem5437526) (@lem5437542)). Qed.
Lemma lem5437545 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5437546 : term291 = term214.
Proof. exact (@lem5437545 term214). Qed.
Lemma lem5437547 : term298 = term214.
Proof. exact (TRANS (@lem5437543) (@lem5437546)). Qed.
Lemma lem5437548 (_70507 : int) : (term229 _70507) = (term229 _70507).
Proof. exact (eq_refl (term229 _70507)). Qed.
Lemma lem5437549 (_70507 : int) : (term289 _70507) = (term311 _70507).
Proof. exact (MK_COMB (@lem5437548 _70507) (@lem5437547)). Qed.
Lemma lem5437550 (_70507 : int) : (term311 _70507) = (real_of_int _70507).
Proof. exact (@lem1982723 (real_of_int _70507)). Qed.
Lemma lem5437551 (_70507 : int) : (term289 _70507) = (real_of_int _70507).
Proof. exact (TRANS (@lem5437549 _70507) (@lem5437550 _70507)). Qed.
Lemma lem5437553 (_70507 : int) : (term288 _70507) = (real_of_int _70507).
Proof. exact (TRANS (@lem5437517 _70507) (@lem5437551 _70507)). Qed.
Lemma lem5437554 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5437555 (_70507 : int) : (term312 _70507) = (term313 _70507).
Proof. exact (MK_COMB (@lem5437554) (@lem5437553 _70507)). Qed.
Lemma lem5437556 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5437557 (_70507 : int) : (term287 _70507) = (term314 _70507).
Proof. exact (MK_COMB (@lem5437555 _70507) (@lem5437556)). Qed.
Lemma lem5437558 (_70507 : int) : (term217 _70507) = (term314 _70507).
Proof. exact (TRANS (@lem5437511 _70507) (@lem5437557 _70507)). Qed.
Lemma lem5437559 (_70508 : int) : (term217 _70508) = (term287 _70508).
Proof. exact (@lem1988287 (real_of_int _70508) term214). Qed.
Lemma lem5437565 (_70508 : int) : (term288 _70508) = (term289 _70508).
Proof. exact (@lem1982792 (real_of_int _70508) term214). Qed.
Lemma lem5437567 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5437568 : term214 = term291.
Proof. exact (@lem5437567 (NUMERAL 0)). Qed.
Lemma lem5437570 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5437571 : term294 = term295.
Proof. exact (@lem5437570 term228). Qed.
Lemma lem5437572 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5437573 : term296 = term297.
Proof. exact (MK_COMB (@lem5437572) (@lem5437571)). Qed.
Lemma lem5437574 : term298 = term299.
Proof. exact (MK_COMB (@lem5437573) (@lem5437568)). Qed.
Lemma lem5437575 : term299 = term300.
Proof. exact (@lem1981613 term294 term214 term227 term227). Qed.
Lemma lem5437577 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5437578 : term303 = term304.
Proof. exact (@lem5437577 term228 term228). Qed.
Lemma lem5437579 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5437580 : term306 = term228.
Proof. exact (EQ_MP (@lem5437579) (@lem940073)). Qed.
Lemma lem5437581 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5437582 : term304 = term227.
Proof. exact (MK_COMB (@lem5437581) (@lem5437580)). Qed.
Lemma lem5437583 : term303 = term227.
Proof. exact (TRANS (@lem5437578) (@lem5437582)). Qed.
Lemma lem5437585 (x : nat) : (term307 x) = term214.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5437586 : term298 = term214.
Proof. exact (@lem5437585 term228). Qed.
Lemma lem5437587 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5437588 : term308 = term309.
Proof. exact (MK_COMB (@lem5437587) (@lem5437586)). Qed.
Lemma lem5437589 : term300 = term291.
Proof. exact (MK_COMB (@lem5437588) (@lem5437583)). Qed.
Lemma lem5437590 : term299 = term291.
Proof. exact (TRANS (@lem5437575) (@lem5437589)). Qed.
Lemma lem5437591 : term298 = term291.
Proof. exact (TRANS (@lem5437574) (@lem5437590)). Qed.
Lemma lem5437593 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5437594 : term291 = term214.
Proof. exact (@lem5437593 term214). Qed.
Lemma lem5437595 : term298 = term214.
Proof. exact (TRANS (@lem5437591) (@lem5437594)). Qed.
Lemma lem5437596 (_70508 : int) : (term229 _70508) = (term229 _70508).
Proof. exact (eq_refl (term229 _70508)). Qed.
Lemma lem5437597 (_70508 : int) : (term289 _70508) = (term311 _70508).
Proof. exact (MK_COMB (@lem5437596 _70508) (@lem5437595)). Qed.
Lemma lem5437598 (_70508 : int) : (term311 _70508) = (real_of_int _70508).
Proof. exact (@lem1982723 (real_of_int _70508)). Qed.
Lemma lem5437599 (_70508 : int) : (term289 _70508) = (real_of_int _70508).
Proof. exact (TRANS (@lem5437597 _70508) (@lem5437598 _70508)). Qed.
Lemma lem5437601 (_70508 : int) : (term288 _70508) = (real_of_int _70508).
Proof. exact (TRANS (@lem5437565 _70508) (@lem5437599 _70508)). Qed.
Lemma lem5437602 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5437603 (_70508 : int) : (term312 _70508) = (term313 _70508).
Proof. exact (MK_COMB (@lem5437602) (@lem5437601 _70508)). Qed.
Lemma lem5437604 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5437605 (_70508 : int) : (term287 _70508) = (term314 _70508).
Proof. exact (MK_COMB (@lem5437603 _70508) (@lem5437604)). Qed.
Lemma lem5437606 (_70508 : int) : (term217 _70508) = (term314 _70508).
Proof. exact (TRANS (@lem5437559 _70508) (@lem5437605 _70508)). Qed.
Lemma lem5437607 (_70504 : int) (_70508 : int) : (term233 _70508 _70504) = (term315 _70504 _70508).
Proof. exact (@lem1988287 (real_of_int _70504) (term230 _70508)). Qed.
Lemma lem5437619 (_70504 : int) (_70508 : int) : (term316 _70504 _70508) = (term317 _70504 _70508).
Proof. exact (@lem1982792 (real_of_int _70504) (term230 _70508)). Qed.
Lemma lem5437620 (_70508 : int) : (term318 _70508) = (term319 _70508).
Proof. exact (@lem1982781 (real_of_int _70508) term294 term227). Qed.
Lemma lem5437622 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5437623 : term227 = term320.
Proof. exact (@lem5437622 term228). Qed.
Lemma lem5437625 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5437626 : term294 = term295.
Proof. exact (@lem5437625 term228). Qed.
Lemma lem5437627 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5437628 : term296 = term297.
Proof. exact (MK_COMB (@lem5437627) (@lem5437626)). Qed.
Lemma lem5437629 : term321 = term322.
Proof. exact (MK_COMB (@lem5437628) (@lem5437623)). Qed.
Lemma lem5437630 : term322 = term323.
Proof. exact (@lem1981613 term294 term227 term227 term227). Qed.
Lemma lem5437632 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5437633 : term303 = term304.
Proof. exact (@lem5437632 term228 term228). Qed.
Lemma lem5437634 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5437635 : term306 = term228.
Proof. exact (EQ_MP (@lem5437634) (@lem940073)). Qed.
Lemma lem5437636 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5437637 : term304 = term227.
Proof. exact (MK_COMB (@lem5437636) (@lem5437635)). Qed.
Lemma lem5437638 : term303 = term227.
Proof. exact (TRANS (@lem5437633) (@lem5437637)). Qed.
Lemma lem5437640 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5437641 : term321 = term326.
Proof. exact (@lem5437640 term228 term228). Qed.
Lemma lem5437642 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5437643 : term306 = term228.
Proof. exact (EQ_MP (@lem5437642) (@lem940073)). Qed.
Lemma lem5437644 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5437645 : term304 = term227.
Proof. exact (MK_COMB (@lem5437644) (@lem5437643)). Qed.
Lemma lem5437646 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5437647 : term326 = term294.
Proof. exact (MK_COMB (@lem5437646) (@lem5437645)). Qed.
Lemma lem5437648 : term321 = term294.
Proof. exact (TRANS (@lem5437641) (@lem5437647)). Qed.
Lemma lem5437649 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5437650 : term327 = term328.
Proof. exact (MK_COMB (@lem5437649) (@lem5437648)). Qed.
Lemma lem5437651 : term323 = term295.
Proof. exact (MK_COMB (@lem5437650) (@lem5437638)). Qed.
Lemma lem5437652 : term322 = term295.
Proof. exact (TRANS (@lem5437630) (@lem5437651)). Qed.
Lemma lem5437653 : term321 = term295.
Proof. exact (TRANS (@lem5437629) (@lem5437652)). Qed.
Lemma lem5437655 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5437656 : term295 = term294.
Proof. exact (@lem5437655 term294). Qed.
Lemma lem5437657 : term321 = term294.
Proof. exact (TRANS (@lem5437653) (@lem5437656)). Qed.
Lemma lem5437660 (_70508 : int) : (term329 _70508) = (term329 _70508).
Proof. exact (eq_refl (term329 _70508)). Qed.
Lemma lem5437661 (_70508 : int) : (term319 _70508) = (term330 _70508).
Proof. exact (MK_COMB (@lem5437660 _70508) (@lem5437657)). Qed.
Lemma lem5437662 (_70508 : int) : (term318 _70508) = (term330 _70508).
Proof. exact (TRANS (@lem5437620 _70508) (@lem5437661 _70508)). Qed.
Lemma lem5437663 (_70504 : int) : (term229 _70504) = (term229 _70504).
Proof. exact (eq_refl (term229 _70504)). Qed.
Lemma lem5437666 (_70504 : int) (_70508 : int) : (term317 _70504 _70508) = (term331 _70504 _70508).
Proof. exact (MK_COMB (@lem5437663 _70504) (@lem5437662 _70508)). Qed.
Lemma lem5437668 (_70504 : int) (_70508 : int) : (term316 _70504 _70508) = (term331 _70504 _70508).
Proof. exact (TRANS (@lem5437619 _70504 _70508) (@lem5437666 _70504 _70508)). Qed.
Lemma lem5437669 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5437670 (_70504 : int) (_70508 : int) : (term332 _70504 _70508) = (term333 _70504 _70508).
Proof. exact (MK_COMB (@lem5437669) (@lem5437668 _70504 _70508)). Qed.
Lemma lem5437671 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5437672 (_70504 : int) (_70508 : int) : (term315 _70504 _70508) = (term334 _70504 _70508).
Proof. exact (MK_COMB (@lem5437670 _70504 _70508) (@lem5437671)). Qed.
Lemma lem5437673 (_70504 : int) (_70508 : int) : (term233 _70508 _70504) = (term334 _70504 _70508).
Proof. exact (TRANS (@lem5437607 _70504 _70508) (@lem5437672 _70504 _70508)). Qed.
Lemma lem5437674 (_70508 : int) (_70505 : int) : (term233 _70505 _70508) = (term315 _70508 _70505).
Proof. exact (@lem1988287 (real_of_int _70508) (term230 _70505)). Qed.
Lemma lem5437686 (_70508 : int) (_70505 : int) : (term316 _70508 _70505) = (term317 _70508 _70505).
Proof. exact (@lem1982792 (real_of_int _70508) (term230 _70505)). Qed.
Lemma lem5437687 (_70505 : int) : (term318 _70505) = (term319 _70505).
Proof. exact (@lem1982781 (real_of_int _70505) term294 term227). Qed.
Lemma lem5437689 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5437690 : term227 = term320.
Proof. exact (@lem5437689 term228). Qed.
Lemma lem5437692 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5437693 : term294 = term295.
Proof. exact (@lem5437692 term228). Qed.
Lemma lem5437694 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5437695 : term296 = term297.
Proof. exact (MK_COMB (@lem5437694) (@lem5437693)). Qed.
Lemma lem5437696 : term321 = term322.
Proof. exact (MK_COMB (@lem5437695) (@lem5437690)). Qed.
Lemma lem5437697 : term322 = term323.
Proof. exact (@lem1981613 term294 term227 term227 term227). Qed.
Lemma lem5437699 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5437700 : term303 = term304.
Proof. exact (@lem5437699 term228 term228). Qed.
Lemma lem5437701 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5437702 : term306 = term228.
Proof. exact (EQ_MP (@lem5437701) (@lem940073)). Qed.
Lemma lem5437703 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5437704 : term304 = term227.
Proof. exact (MK_COMB (@lem5437703) (@lem5437702)). Qed.
Lemma lem5437705 : term303 = term227.
Proof. exact (TRANS (@lem5437700) (@lem5437704)). Qed.
Lemma lem5437707 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5437708 : term321 = term326.
Proof. exact (@lem5437707 term228 term228). Qed.
Lemma lem5437709 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5437710 : term306 = term228.
Proof. exact (EQ_MP (@lem5437709) (@lem940073)). Qed.
Lemma lem5437711 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5437712 : term304 = term227.
Proof. exact (MK_COMB (@lem5437711) (@lem5437710)). Qed.
Lemma lem5437713 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5437714 : term326 = term294.
Proof. exact (MK_COMB (@lem5437713) (@lem5437712)). Qed.
Lemma lem5437715 : term321 = term294.
Proof. exact (TRANS (@lem5437708) (@lem5437714)). Qed.
Lemma lem5437716 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5437717 : term327 = term328.
Proof. exact (MK_COMB (@lem5437716) (@lem5437715)). Qed.
Lemma lem5437718 : term323 = term295.
Proof. exact (MK_COMB (@lem5437717) (@lem5437705)). Qed.
Lemma lem5437719 : term322 = term295.
Proof. exact (TRANS (@lem5437697) (@lem5437718)). Qed.
Lemma lem5437720 : term321 = term295.
Proof. exact (TRANS (@lem5437696) (@lem5437719)). Qed.
Lemma lem5437722 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5437723 : term295 = term294.
Proof. exact (@lem5437722 term294). Qed.
Lemma lem5437724 : term321 = term294.
Proof. exact (TRANS (@lem5437720) (@lem5437723)). Qed.
Lemma lem5437727 (_70505 : int) : (term329 _70505) = (term329 _70505).
Proof. exact (eq_refl (term329 _70505)). Qed.
Lemma lem5437728 (_70505 : int) : (term319 _70505) = (term330 _70505).
Proof. exact (MK_COMB (@lem5437727 _70505) (@lem5437724)). Qed.
Lemma lem5437729 (_70505 : int) : (term318 _70505) = (term330 _70505).
Proof. exact (TRANS (@lem5437687 _70505) (@lem5437728 _70505)). Qed.
Lemma lem5437730 (_70508 : int) : (term229 _70508) = (term229 _70508).
Proof. exact (eq_refl (term229 _70508)). Qed.
Lemma lem5437731 (_70508 : int) (_70505 : int) : (term317 _70508 _70505) = (term331 _70508 _70505).
Proof. exact (MK_COMB (@lem5437730 _70508) (@lem5437729 _70505)). Qed.
Lemma lem5437736 (_70505 : int) (_70508 : int) : (term331 _70508 _70505) = (term335 _70505 _70508).
Proof. exact (@lem1982757 (term336 _70505) (real_of_int _70508) term294). Qed.
Lemma lem5437737 (_70505 : int) (_70508 : int) : (term317 _70508 _70505) = (term335 _70505 _70508).
Proof. exact (TRANS (@lem5437731 _70508 _70505) (@lem5437736 _70505 _70508)). Qed.
Lemma lem5437739 (_70505 : int) (_70508 : int) : (term316 _70508 _70505) = (term335 _70505 _70508).
Proof. exact (TRANS (@lem5437686 _70508 _70505) (@lem5437737 _70505 _70508)). Qed.
Lemma lem5437740 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5437741 (_70505 : int) (_70508 : int) : (term332 _70508 _70505) = (term337 _70505 _70508).
Proof. exact (MK_COMB (@lem5437740) (@lem5437739 _70505 _70508)). Qed.
Lemma lem5437742 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5437743 (_70505 : int) (_70508 : int) : (term315 _70508 _70505) = (term338 _70505 _70508).
Proof. exact (MK_COMB (@lem5437741 _70505 _70508) (@lem5437742)). Qed.
Lemma lem5437744 (_70505 : int) (_70508 : int) : (term233 _70505 _70508) = (term338 _70505 _70508).
Proof. exact (TRANS (@lem5437674 _70508 _70505) (@lem5437743 _70505 _70508)). Qed.
Lemma lem5437745 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5437746 (_70504 : int) (_70508 : int) : (term235 _70508 _70504) = (term339 _70504 _70508).
Proof. exact (MK_COMB (@lem5437745) (@lem5437673 _70504 _70508)). Qed.
Lemma lem5437747 (_70504 : int) (_70505 : int) (_70508 : int) : (term236 _70504 _70505 _70508) = (term340 _70504 _70505 _70508).
Proof. exact (MK_COMB (@lem5437746 _70504 _70508) (@lem5437744 _70505 _70508)). Qed.
Lemma lem5437748 (_70506 : int) (_70508 : int) : (term233 _70508 _70506) = (term315 _70506 _70508).
Proof. exact (@lem1988287 (real_of_int _70506) (term230 _70508)). Qed.
Lemma lem5437760 (_70506 : int) (_70508 : int) : (term316 _70506 _70508) = (term317 _70506 _70508).
Proof. exact (@lem1982792 (real_of_int _70506) (term230 _70508)). Qed.
Lemma lem5437761 (_70508 : int) : (term318 _70508) = (term319 _70508).
Proof. exact (@lem1982781 (real_of_int _70508) term294 term227). Qed.
Lemma lem5437763 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5437764 : term227 = term320.
Proof. exact (@lem5437763 term228). Qed.
Lemma lem5437766 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5437767 : term294 = term295.
Proof. exact (@lem5437766 term228). Qed.
Lemma lem5437768 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5437769 : term296 = term297.
Proof. exact (MK_COMB (@lem5437768) (@lem5437767)). Qed.
Lemma lem5437770 : term321 = term322.
Proof. exact (MK_COMB (@lem5437769) (@lem5437764)). Qed.
Lemma lem5437771 : term322 = term323.
Proof. exact (@lem1981613 term294 term227 term227 term227). Qed.
Lemma lem5437773 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5437774 : term303 = term304.
Proof. exact (@lem5437773 term228 term228). Qed.
Lemma lem5437775 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5437776 : term306 = term228.
Proof. exact (EQ_MP (@lem5437775) (@lem940073)). Qed.
Lemma lem5437777 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5437778 : term304 = term227.
Proof. exact (MK_COMB (@lem5437777) (@lem5437776)). Qed.
Lemma lem5437779 : term303 = term227.
Proof. exact (TRANS (@lem5437774) (@lem5437778)). Qed.
Lemma lem5437781 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5437782 : term321 = term326.
Proof. exact (@lem5437781 term228 term228). Qed.
Lemma lem5437783 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5437784 : term306 = term228.
Proof. exact (EQ_MP (@lem5437783) (@lem940073)). Qed.
Lemma lem5437785 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5437786 : term304 = term227.
Proof. exact (MK_COMB (@lem5437785) (@lem5437784)). Qed.
Lemma lem5437787 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5437788 : term326 = term294.
Proof. exact (MK_COMB (@lem5437787) (@lem5437786)). Qed.
Lemma lem5437789 : term321 = term294.
Proof. exact (TRANS (@lem5437782) (@lem5437788)). Qed.
Lemma lem5437790 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5437791 : term327 = term328.
Proof. exact (MK_COMB (@lem5437790) (@lem5437789)). Qed.
Lemma lem5437792 : term323 = term295.
Proof. exact (MK_COMB (@lem5437791) (@lem5437779)). Qed.
Lemma lem5437793 : term322 = term295.
Proof. exact (TRANS (@lem5437771) (@lem5437792)). Qed.
Lemma lem5437794 : term321 = term295.
Proof. exact (TRANS (@lem5437770) (@lem5437793)). Qed.
Lemma lem5437796 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5437797 : term295 = term294.
Proof. exact (@lem5437796 term294). Qed.
Lemma lem5437798 : term321 = term294.
Proof. exact (TRANS (@lem5437794) (@lem5437797)). Qed.
Lemma lem5437801 (_70508 : int) : (term329 _70508) = (term329 _70508).
Proof. exact (eq_refl (term329 _70508)). Qed.
Lemma lem5437802 (_70508 : int) : (term319 _70508) = (term330 _70508).
Proof. exact (MK_COMB (@lem5437801 _70508) (@lem5437798)). Qed.
Lemma lem5437803 (_70508 : int) : (term318 _70508) = (term330 _70508).
Proof. exact (TRANS (@lem5437761 _70508) (@lem5437802 _70508)). Qed.
Lemma lem5437804 (_70506 : int) : (term229 _70506) = (term229 _70506).
Proof. exact (eq_refl (term229 _70506)). Qed.
Lemma lem5437807 (_70506 : int) (_70508 : int) : (term317 _70506 _70508) = (term331 _70506 _70508).
Proof. exact (MK_COMB (@lem5437804 _70506) (@lem5437803 _70508)). Qed.
Lemma lem5437809 (_70506 : int) (_70508 : int) : (term316 _70506 _70508) = (term331 _70506 _70508).
Proof. exact (TRANS (@lem5437760 _70506 _70508) (@lem5437807 _70506 _70508)). Qed.
Lemma lem5437810 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5437811 (_70506 : int) (_70508 : int) : (term332 _70506 _70508) = (term333 _70506 _70508).
Proof. exact (MK_COMB (@lem5437810) (@lem5437809 _70506 _70508)). Qed.
Lemma lem5437812 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5437813 (_70506 : int) (_70508 : int) : (term315 _70506 _70508) = (term334 _70506 _70508).
Proof. exact (MK_COMB (@lem5437811 _70506 _70508) (@lem5437812)). Qed.
Lemma lem5437814 (_70506 : int) (_70508 : int) : (term233 _70508 _70506) = (term334 _70506 _70508).
Proof. exact (TRANS (@lem5437748 _70506 _70508) (@lem5437813 _70506 _70508)). Qed.
Lemma lem5437815 (_70508 : int) (_70507 : int) : (term233 _70507 _70508) = (term315 _70508 _70507).
Proof. exact (@lem1988287 (real_of_int _70508) (term230 _70507)). Qed.
Lemma lem5437827 (_70508 : int) (_70507 : int) : (term316 _70508 _70507) = (term317 _70508 _70507).
Proof. exact (@lem1982792 (real_of_int _70508) (term230 _70507)). Qed.
Lemma lem5437828 (_70507 : int) : (term318 _70507) = (term319 _70507).
Proof. exact (@lem1982781 (real_of_int _70507) term294 term227). Qed.
Lemma lem5437830 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5437831 : term227 = term320.
Proof. exact (@lem5437830 term228). Qed.
Lemma lem5437833 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5437834 : term294 = term295.
Proof. exact (@lem5437833 term228). Qed.
Lemma lem5437835 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5437836 : term296 = term297.
Proof. exact (MK_COMB (@lem5437835) (@lem5437834)). Qed.
Lemma lem5437837 : term321 = term322.
Proof. exact (MK_COMB (@lem5437836) (@lem5437831)). Qed.
Lemma lem5437838 : term322 = term323.
Proof. exact (@lem1981613 term294 term227 term227 term227). Qed.
Lemma lem5437840 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5437841 : term303 = term304.
Proof. exact (@lem5437840 term228 term228). Qed.
Lemma lem5437842 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5437843 : term306 = term228.
Proof. exact (EQ_MP (@lem5437842) (@lem940073)). Qed.
Lemma lem5437844 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5437845 : term304 = term227.
Proof. exact (MK_COMB (@lem5437844) (@lem5437843)). Qed.
Lemma lem5437846 : term303 = term227.
Proof. exact (TRANS (@lem5437841) (@lem5437845)). Qed.
Lemma lem5437848 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5437849 : term321 = term326.
Proof. exact (@lem5437848 term228 term228). Qed.
Lemma lem5437850 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5437851 : term306 = term228.
Proof. exact (EQ_MP (@lem5437850) (@lem940073)). Qed.
Lemma lem5437852 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5437853 : term304 = term227.
Proof. exact (MK_COMB (@lem5437852) (@lem5437851)). Qed.
Lemma lem5437854 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5437855 : term326 = term294.
Proof. exact (MK_COMB (@lem5437854) (@lem5437853)). Qed.
Lemma lem5437856 : term321 = term294.
Proof. exact (TRANS (@lem5437849) (@lem5437855)). Qed.
Lemma lem5437857 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5437858 : term327 = term328.
Proof. exact (MK_COMB (@lem5437857) (@lem5437856)). Qed.
Lemma lem5437859 : term323 = term295.
Proof. exact (MK_COMB (@lem5437858) (@lem5437846)). Qed.
Lemma lem5437860 : term322 = term295.
Proof. exact (TRANS (@lem5437838) (@lem5437859)). Qed.
Lemma lem5437861 : term321 = term295.
Proof. exact (TRANS (@lem5437837) (@lem5437860)). Qed.
Lemma lem5437863 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5437864 : term295 = term294.
Proof. exact (@lem5437863 term294). Qed.
Lemma lem5437865 : term321 = term294.
Proof. exact (TRANS (@lem5437861) (@lem5437864)). Qed.
Lemma lem5437868 (_70507 : int) : (term329 _70507) = (term329 _70507).
Proof. exact (eq_refl (term329 _70507)). Qed.
Lemma lem5437869 (_70507 : int) : (term319 _70507) = (term330 _70507).
Proof. exact (MK_COMB (@lem5437868 _70507) (@lem5437865)). Qed.
Lemma lem5437870 (_70507 : int) : (term318 _70507) = (term330 _70507).
Proof. exact (TRANS (@lem5437828 _70507) (@lem5437869 _70507)). Qed.
Lemma lem5437871 (_70508 : int) : (term229 _70508) = (term229 _70508).
Proof. exact (eq_refl (term229 _70508)). Qed.
Lemma lem5437872 (_70508 : int) (_70507 : int) : (term317 _70508 _70507) = (term331 _70508 _70507).
Proof. exact (MK_COMB (@lem5437871 _70508) (@lem5437870 _70507)). Qed.
Lemma lem5437877 (_70507 : int) (_70508 : int) : (term331 _70508 _70507) = (term335 _70507 _70508).
Proof. exact (@lem1982757 (term336 _70507) (real_of_int _70508) term294). Qed.
Lemma lem5437878 (_70507 : int) (_70508 : int) : (term317 _70508 _70507) = (term335 _70507 _70508).
Proof. exact (TRANS (@lem5437872 _70508 _70507) (@lem5437877 _70507 _70508)). Qed.
Lemma lem5437880 (_70507 : int) (_70508 : int) : (term316 _70508 _70507) = (term335 _70507 _70508).
Proof. exact (TRANS (@lem5437827 _70508 _70507) (@lem5437878 _70507 _70508)). Qed.
Lemma lem5437881 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5437882 (_70507 : int) (_70508 : int) : (term332 _70508 _70507) = (term337 _70507 _70508).
Proof. exact (MK_COMB (@lem5437881) (@lem5437880 _70507 _70508)). Qed.
Lemma lem5437883 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5437884 (_70507 : int) (_70508 : int) : (term315 _70508 _70507) = (term338 _70507 _70508).
Proof. exact (MK_COMB (@lem5437882 _70507 _70508) (@lem5437883)). Qed.
Lemma lem5437885 (_70507 : int) (_70508 : int) : (term233 _70507 _70508) = (term338 _70507 _70508).
Proof. exact (TRANS (@lem5437815 _70508 _70507) (@lem5437884 _70507 _70508)). Qed.
Lemma lem5437886 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5437887 (_70506 : int) (_70508 : int) : (term235 _70508 _70506) = (term339 _70506 _70508).
Proof. exact (MK_COMB (@lem5437886) (@lem5437814 _70506 _70508)). Qed.
Lemma lem5437888 (_70506 : int) (_70507 : int) (_70508 : int) : (term236 _70506 _70507 _70508) = (term340 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5437887 _70506 _70508) (@lem5437885 _70507 _70508)). Qed.
Lemma lem5437889 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5437890 (_70504 : int) (_70505 : int) (_70508 : int) : (term237 _70504 _70505 _70508) = (term341 _70504 _70505 _70508).
Proof. exact (MK_COMB (@lem5437889) (@lem5437747 _70504 _70505 _70508)). Qed.
Lemma lem5437891 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) : (term238 _70504 _70505 _70506 _70507 _70508) = (term342 _70504 _70505 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5437890 _70504 _70505 _70508) (@lem5437888 _70506 _70507 _70508)). Qed.
Lemma lem5437892 (_70508 : int) (_70504 : int) (_70506 : int) : (term244 _70504 _70506 _70508) = (term343 _70508 _70504 _70506).
Proof. exact (@lem1988287 (real_of_int _70508) (term241 _70504 _70506)). Qed.
Lemma lem5437909 (_70508 : int) (_70504 : int) (_70506 : int) : (term344 _70508 _70504 _70506) = (term345 _70508 _70504 _70506).
Proof. exact (@lem1982792 (real_of_int _70508) (term241 _70504 _70506)). Qed.
Lemma lem5437910 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5437911 (_70508 : int) (_70504 : int) (_70506 : int) : (term346 _70508 _70504 _70506) = (term347 _70508 _70504 _70506).
Proof. exact (MK_COMB (@lem5437910) (@lem5437909 _70508 _70504 _70506)). Qed.
Lemma lem5437912 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5437913 (_70508 : int) (_70504 : int) (_70506 : int) : (term343 _70508 _70504 _70506) = (term348 _70508 _70504 _70506).
Proof. exact (MK_COMB (@lem5437911 _70508 _70504 _70506) (@lem5437912)). Qed.
Lemma lem5437914 (_70508 : int) (_70504 : int) (_70506 : int) : (term244 _70504 _70506 _70508) = (term348 _70508 _70504 _70506).
Proof. exact (TRANS (@lem5437892 _70508 _70504 _70506) (@lem5437913 _70508 _70504 _70506)). Qed.
Lemma lem5437915 (_70505 : int) (_70507 : int) (_70508 : int) : (term249 _70508 _70505 _70507) = (term349 _70505 _70507 _70508).
Proof. exact (@lem1988287 (term247 _70505 _70507) (real_of_int _70508)). Qed.
Lemma lem5437925 (_70505 : int) (_70507 : int) (_70508 : int) : (term350 _70505 _70507 _70508) = (term351 _70505 _70507 _70508).
Proof. exact (@lem1982792 (term247 _70505 _70507) (real_of_int _70508)). Qed.
Lemma lem5437930 (_70508 : int) (_70505 : int) (_70507 : int) : (term351 _70505 _70507 _70508) = (term352 _70508 _70505 _70507).
Proof. exact (@lem1982761 (term336 _70508) (term247 _70505 _70507)). Qed.
Lemma lem5437932 (_70508 : int) (_70505 : int) (_70507 : int) : (term350 _70505 _70507 _70508) = (term352 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5437925 _70505 _70507 _70508) (@lem5437930 _70508 _70505 _70507)). Qed.
Lemma lem5437933 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5437934 (_70508 : int) (_70505 : int) (_70507 : int) : (term353 _70505 _70507 _70508) = (term354 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5437933) (@lem5437932 _70508 _70505 _70507)). Qed.
Lemma lem5437935 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5437936 (_70508 : int) (_70505 : int) (_70507 : int) : (term349 _70505 _70507 _70508) = (term355 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5437934 _70508 _70505 _70507) (@lem5437935)). Qed.
Lemma lem5437937 (_70508 : int) (_70505 : int) (_70507 : int) : (term249 _70508 _70505 _70507) = (term355 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5437915 _70505 _70507 _70508) (@lem5437936 _70508 _70505 _70507)). Qed.
Lemma lem5437938 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5437939 (_70508 : int) (_70504 : int) (_70506 : int) : (term250 _70504 _70506 _70508) = (term356 _70508 _70504 _70506).
Proof. exact (MK_COMB (@lem5437938) (@lem5437914 _70508 _70504 _70506)). Qed.
Lemma lem5437940 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term251 _70504 _70506 _70508 _70505 _70507) = (term357 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5437939 _70508 _70504 _70506) (@lem5437937 _70508 _70505 _70507)). Qed.
Lemma lem5437941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5437942 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) : (term252 _70504 _70505 _70506 _70507 _70508) = (term358 _70504 _70505 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5437941) (@lem5437891 _70504 _70505 _70506 _70507 _70508)). Qed.
Lemma lem5437943 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term253 _70504 _70506 _70508 _70505 _70507) = (term359 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5437942 _70504 _70505 _70506 _70507 _70508) (@lem5437940 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5437944 (_70508 : int) (_70504 : int) : (term209 _70504 _70508) = (term360 _70508 _70504).
Proof. exact (@lem1988287 (real_of_int _70508) (real_of_int _70504)). Qed.
Lemma lem5437950 (_70508 : int) (_70504 : int) : (term361 _70508 _70504) = (term362 _70508 _70504).
Proof. exact (@lem1982792 (real_of_int _70508) (real_of_int _70504)). Qed.
Lemma lem5437955 (_70504 : int) (_70508 : int) : (term362 _70508 _70504) = (term363 _70504 _70508).
Proof. exact (@lem1982761 (term336 _70504) (real_of_int _70508)). Qed.
Lemma lem5437957 (_70504 : int) (_70508 : int) : (term361 _70508 _70504) = (term363 _70504 _70508).
Proof. exact (TRANS (@lem5437950 _70508 _70504) (@lem5437955 _70504 _70508)). Qed.
Lemma lem5437958 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5437959 (_70504 : int) (_70508 : int) : (term364 _70508 _70504) = (term365 _70504 _70508).
Proof. exact (MK_COMB (@lem5437958) (@lem5437957 _70504 _70508)). Qed.
Lemma lem5437960 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5437961 (_70504 : int) (_70508 : int) : (term360 _70508 _70504) = (term366 _70504 _70508).
Proof. exact (MK_COMB (@lem5437959 _70504 _70508) (@lem5437960)). Qed.
Lemma lem5437962 (_70504 : int) (_70508 : int) : (term209 _70504 _70508) = (term366 _70504 _70508).
Proof. exact (TRANS (@lem5437944 _70508 _70504) (@lem5437961 _70504 _70508)). Qed.
Lemma lem5437963 (_70505 : int) (_70508 : int) : (term209 _70508 _70505) = (term360 _70505 _70508).
Proof. exact (@lem1988287 (real_of_int _70505) (real_of_int _70508)). Qed.
Lemma lem5437976 (_70505 : int) (_70508 : int) : (term361 _70505 _70508) = (term362 _70505 _70508).
Proof. exact (@lem1982792 (real_of_int _70505) (real_of_int _70508)). Qed.
Lemma lem5437977 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5437978 (_70505 : int) (_70508 : int) : (term364 _70505 _70508) = (term367 _70505 _70508).
Proof. exact (MK_COMB (@lem5437977) (@lem5437976 _70505 _70508)). Qed.
Lemma lem5437979 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5437980 (_70505 : int) (_70508 : int) : (term360 _70505 _70508) = (term368 _70505 _70508).
Proof. exact (MK_COMB (@lem5437978 _70505 _70508) (@lem5437979)). Qed.
Lemma lem5437981 (_70505 : int) (_70508 : int) : (term209 _70508 _70505) = (term368 _70505 _70508).
Proof. exact (TRANS (@lem5437963 _70505 _70508) (@lem5437980 _70505 _70508)). Qed.
Lemma lem5437982 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5437983 (_70504 : int) (_70508 : int) : (term254 _70504 _70508) = (term369 _70504 _70508).
Proof. exact (MK_COMB (@lem5437982) (@lem5437962 _70504 _70508)). Qed.
Lemma lem5437984 (_70504 : int) (_70505 : int) (_70508 : int) : (term255 _70504 _70508 _70505) = (term370 _70504 _70505 _70508).
Proof. exact (MK_COMB (@lem5437983 _70504 _70508) (@lem5437981 _70505 _70508)). Qed.
Lemma lem5437985 (_70508 : int) (_70506 : int) : (term209 _70506 _70508) = (term360 _70508 _70506).
Proof. exact (@lem1988287 (real_of_int _70508) (real_of_int _70506)). Qed.
Lemma lem5437991 (_70508 : int) (_70506 : int) : (term361 _70508 _70506) = (term362 _70508 _70506).
Proof. exact (@lem1982792 (real_of_int _70508) (real_of_int _70506)). Qed.
Lemma lem5437996 (_70506 : int) (_70508 : int) : (term362 _70508 _70506) = (term363 _70506 _70508).
Proof. exact (@lem1982761 (term336 _70506) (real_of_int _70508)). Qed.
Lemma lem5437998 (_70506 : int) (_70508 : int) : (term361 _70508 _70506) = (term363 _70506 _70508).
Proof. exact (TRANS (@lem5437991 _70508 _70506) (@lem5437996 _70506 _70508)). Qed.
Lemma lem5437999 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5438000 (_70506 : int) (_70508 : int) : (term364 _70508 _70506) = (term365 _70506 _70508).
Proof. exact (MK_COMB (@lem5437999) (@lem5437998 _70506 _70508)). Qed.
Lemma lem5438001 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5438002 (_70506 : int) (_70508 : int) : (term360 _70508 _70506) = (term366 _70506 _70508).
Proof. exact (MK_COMB (@lem5438000 _70506 _70508) (@lem5438001)). Qed.
Lemma lem5438003 (_70506 : int) (_70508 : int) : (term209 _70506 _70508) = (term366 _70506 _70508).
Proof. exact (TRANS (@lem5437985 _70508 _70506) (@lem5438002 _70506 _70508)). Qed.
Lemma lem5438004 (_70507 : int) (_70508 : int) : (term209 _70508 _70507) = (term360 _70507 _70508).
Proof. exact (@lem1988287 (real_of_int _70507) (real_of_int _70508)). Qed.
Lemma lem5438017 (_70507 : int) (_70508 : int) : (term361 _70507 _70508) = (term362 _70507 _70508).
Proof. exact (@lem1982792 (real_of_int _70507) (real_of_int _70508)). Qed.
Lemma lem5438018 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5438019 (_70507 : int) (_70508 : int) : (term364 _70507 _70508) = (term367 _70507 _70508).
Proof. exact (MK_COMB (@lem5438018) (@lem5438017 _70507 _70508)). Qed.
Lemma lem5438020 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5438021 (_70507 : int) (_70508 : int) : (term360 _70507 _70508) = (term368 _70507 _70508).
Proof. exact (MK_COMB (@lem5438019 _70507 _70508) (@lem5438020)). Qed.
Lemma lem5438022 (_70507 : int) (_70508 : int) : (term209 _70508 _70507) = (term368 _70507 _70508).
Proof. exact (TRANS (@lem5438004 _70507 _70508) (@lem5438021 _70507 _70508)). Qed.
Lemma lem5438023 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5438024 (_70506 : int) (_70508 : int) : (term254 _70506 _70508) = (term369 _70506 _70508).
Proof. exact (MK_COMB (@lem5438023) (@lem5438003 _70506 _70508)). Qed.
Lemma lem5438025 (_70506 : int) (_70507 : int) (_70508 : int) : (term255 _70506 _70508 _70507) = (term370 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5438024 _70506 _70508) (@lem5438022 _70507 _70508)). Qed.
Lemma lem5438026 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5438027 (_70504 : int) (_70505 : int) (_70508 : int) : (term256 _70504 _70508 _70505) = (term371 _70504 _70505 _70508).
Proof. exact (MK_COMB (@lem5438026) (@lem5437984 _70504 _70505 _70508)). Qed.
Lemma lem5438028 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) : (term257 _70504 _70505 _70506 _70508 _70507) = (term372 _70504 _70505 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5438027 _70504 _70505 _70508) (@lem5438025 _70506 _70507 _70508)). Qed.
Lemma lem5438029 (_70504 : int) (_70506 : int) (_70508 : int) : (term260 _70508 _70504 _70506) = (term373 _70504 _70506 _70508).
Proof. exact (@lem1988287 (term241 _70504 _70506) (term230 _70508)). Qed.
Lemma lem5438045 (_70504 : int) (_70506 : int) (_70508 : int) : (term374 _70504 _70506 _70508) = (term375 _70504 _70506 _70508).
Proof. exact (@lem1982792 (term241 _70504 _70506) (term230 _70508)). Qed.
Lemma lem5438046 (_70508 : int) : (term318 _70508) = (term319 _70508).
Proof. exact (@lem1982781 (real_of_int _70508) term294 term227). Qed.
Lemma lem5438048 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5438049 : term227 = term320.
Proof. exact (@lem5438048 term228). Qed.
Lemma lem5438051 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5438052 : term294 = term295.
Proof. exact (@lem5438051 term228). Qed.
Lemma lem5438053 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5438054 : term296 = term297.
Proof. exact (MK_COMB (@lem5438053) (@lem5438052)). Qed.
Lemma lem5438055 : term321 = term322.
Proof. exact (MK_COMB (@lem5438054) (@lem5438049)). Qed.
Lemma lem5438056 : term322 = term323.
Proof. exact (@lem1981613 term294 term227 term227 term227). Qed.
Lemma lem5438058 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5438059 : term303 = term304.
Proof. exact (@lem5438058 term228 term228). Qed.
Lemma lem5438060 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5438061 : term306 = term228.
Proof. exact (EQ_MP (@lem5438060) (@lem940073)). Qed.
Lemma lem5438062 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5438063 : term304 = term227.
Proof. exact (MK_COMB (@lem5438062) (@lem5438061)). Qed.
Lemma lem5438064 : term303 = term227.
Proof. exact (TRANS (@lem5438059) (@lem5438063)). Qed.
Lemma lem5438066 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5438067 : term321 = term326.
Proof. exact (@lem5438066 term228 term228). Qed.
Lemma lem5438068 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5438069 : term306 = term228.
Proof. exact (EQ_MP (@lem5438068) (@lem940073)). Qed.
Lemma lem5438070 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5438071 : term304 = term227.
Proof. exact (MK_COMB (@lem5438070) (@lem5438069)). Qed.
Lemma lem5438072 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5438073 : term326 = term294.
Proof. exact (MK_COMB (@lem5438072) (@lem5438071)). Qed.
Lemma lem5438074 : term321 = term294.
Proof. exact (TRANS (@lem5438067) (@lem5438073)). Qed.
Lemma lem5438075 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5438076 : term327 = term328.
Proof. exact (MK_COMB (@lem5438075) (@lem5438074)). Qed.
Lemma lem5438077 : term323 = term295.
Proof. exact (MK_COMB (@lem5438076) (@lem5438064)). Qed.
Lemma lem5438078 : term322 = term295.
Proof. exact (TRANS (@lem5438056) (@lem5438077)). Qed.
Lemma lem5438079 : term321 = term295.
Proof. exact (TRANS (@lem5438055) (@lem5438078)). Qed.
Lemma lem5438081 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5438082 : term295 = term294.
Proof. exact (@lem5438081 term294). Qed.
Lemma lem5438083 : term321 = term294.
Proof. exact (TRANS (@lem5438079) (@lem5438082)). Qed.
Lemma lem5438086 (_70508 : int) : (term329 _70508) = (term329 _70508).
Proof. exact (eq_refl (term329 _70508)). Qed.
Lemma lem5438087 (_70508 : int) : (term319 _70508) = (term330 _70508).
Proof. exact (MK_COMB (@lem5438086 _70508) (@lem5438083)). Qed.
Lemma lem5438088 (_70508 : int) : (term318 _70508) = (term330 _70508).
Proof. exact (TRANS (@lem5438046 _70508) (@lem5438087 _70508)). Qed.
Lemma lem5438089 (_70504 : int) (_70506 : int) : (term376 _70504 _70506) = (term376 _70504 _70506).
Proof. exact (eq_refl (term376 _70504 _70506)). Qed.
Lemma lem5438090 (_70504 : int) (_70506 : int) (_70508 : int) : (term375 _70504 _70506 _70508) = (term377 _70504 _70506 _70508).
Proof. exact (MK_COMB (@lem5438089 _70504 _70506) (@lem5438088 _70508)). Qed.
Lemma lem5438095 (_70508 : int) (_70504 : int) (_70506 : int) : (term377 _70504 _70506 _70508) = (term378 _70508 _70504 _70506).
Proof. exact (@lem1982757 (term336 _70508) (term241 _70504 _70506) term294). Qed.
Lemma lem5438096 (_70508 : int) (_70504 : int) (_70506 : int) : (term375 _70504 _70506 _70508) = (term378 _70508 _70504 _70506).
Proof. exact (TRANS (@lem5438090 _70504 _70506 _70508) (@lem5438095 _70508 _70504 _70506)). Qed.
Lemma lem5438098 (_70508 : int) (_70504 : int) (_70506 : int) : (term374 _70504 _70506 _70508) = (term378 _70508 _70504 _70506).
Proof. exact (TRANS (@lem5438045 _70504 _70506 _70508) (@lem5438096 _70508 _70504 _70506)). Qed.
Lemma lem5438099 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5438100 (_70508 : int) (_70504 : int) (_70506 : int) : (term379 _70504 _70506 _70508) = (term380 _70508 _70504 _70506).
Proof. exact (MK_COMB (@lem5438099) (@lem5438098 _70508 _70504 _70506)). Qed.
Lemma lem5438101 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5438102 (_70508 : int) (_70504 : int) (_70506 : int) : (term373 _70504 _70506 _70508) = (term381 _70508 _70504 _70506).
Proof. exact (MK_COMB (@lem5438100 _70508 _70504 _70506) (@lem5438101)). Qed.
Lemma lem5438103 (_70508 : int) (_70504 : int) (_70506 : int) : (term260 _70508 _70504 _70506) = (term381 _70508 _70504 _70506).
Proof. exact (TRANS (@lem5438029 _70504 _70506 _70508) (@lem5438102 _70508 _70504 _70506)). Qed.
Lemma lem5438104 (_70508 : int) (_70505 : int) (_70507 : int) : (term271 _70505 _70507 _70508) = (term382 _70508 _70505 _70507).
Proof. exact (@lem1988287 (real_of_int _70508) (term268 _70505 _70507)). Qed.
Lemma lem5438120 (_70508 : int) (_70505 : int) (_70507 : int) : (term383 _70508 _70505 _70507) = (term384 _70508 _70505 _70507).
Proof. exact (@lem1982792 (real_of_int _70508) (term268 _70505 _70507)). Qed.
Lemma lem5438121 (_70505 : int) (_70507 : int) : (term385 _70505 _70507) = (term386 _70505 _70507).
Proof. exact (@lem1982781 (term247 _70505 _70507) term294 term227). Qed.
Lemma lem5438123 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5438124 : term227 = term320.
Proof. exact (@lem5438123 term228). Qed.
Lemma lem5438126 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5438127 : term294 = term295.
Proof. exact (@lem5438126 term228). Qed.
Lemma lem5438128 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5438129 : term296 = term297.
Proof. exact (MK_COMB (@lem5438128) (@lem5438127)). Qed.
Lemma lem5438130 : term321 = term322.
Proof. exact (MK_COMB (@lem5438129) (@lem5438124)). Qed.
Lemma lem5438131 : term322 = term323.
Proof. exact (@lem1981613 term294 term227 term227 term227). Qed.
Lemma lem5438133 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5438134 : term303 = term304.
Proof. exact (@lem5438133 term228 term228). Qed.
Lemma lem5438135 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5438136 : term306 = term228.
Proof. exact (EQ_MP (@lem5438135) (@lem940073)). Qed.
Lemma lem5438137 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5438138 : term304 = term227.
Proof. exact (MK_COMB (@lem5438137) (@lem5438136)). Qed.
Lemma lem5438139 : term303 = term227.
Proof. exact (TRANS (@lem5438134) (@lem5438138)). Qed.
Lemma lem5438141 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5438142 : term321 = term326.
Proof. exact (@lem5438141 term228 term228). Qed.
Lemma lem5438143 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5438144 : term306 = term228.
Proof. exact (EQ_MP (@lem5438143) (@lem940073)). Qed.
Lemma lem5438145 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5438146 : term304 = term227.
Proof. exact (MK_COMB (@lem5438145) (@lem5438144)). Qed.
Lemma lem5438147 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5438148 : term326 = term294.
Proof. exact (MK_COMB (@lem5438147) (@lem5438146)). Qed.
Lemma lem5438149 : term321 = term294.
Proof. exact (TRANS (@lem5438142) (@lem5438148)). Qed.
Lemma lem5438150 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5438151 : term327 = term328.
Proof. exact (MK_COMB (@lem5438150) (@lem5438149)). Qed.
Lemma lem5438152 : term323 = term295.
Proof. exact (MK_COMB (@lem5438151) (@lem5438139)). Qed.
Lemma lem5438153 : term322 = term295.
Proof. exact (TRANS (@lem5438131) (@lem5438152)). Qed.
Lemma lem5438154 : term321 = term295.
Proof. exact (TRANS (@lem5438130) (@lem5438153)). Qed.
Lemma lem5438156 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5438157 : term295 = term294.
Proof. exact (@lem5438156 term294). Qed.
Lemma lem5438158 : term321 = term294.
Proof. exact (TRANS (@lem5438154) (@lem5438157)). Qed.
Lemma lem5438161 (_70505 : int) (_70507 : int) : (term387 _70505 _70507) = (term387 _70505 _70507).
Proof. exact (eq_refl (term387 _70505 _70507)). Qed.
Lemma lem5438162 (_70505 : int) (_70507 : int) : (term386 _70505 _70507) = (term388 _70505 _70507).
Proof. exact (MK_COMB (@lem5438161 _70505 _70507) (@lem5438158)). Qed.
Lemma lem5438163 (_70505 : int) (_70507 : int) : (term385 _70505 _70507) = (term388 _70505 _70507).
Proof. exact (TRANS (@lem5438121 _70505 _70507) (@lem5438162 _70505 _70507)). Qed.
Lemma lem5438164 (_70508 : int) : (term229 _70508) = (term229 _70508).
Proof. exact (eq_refl (term229 _70508)). Qed.
Lemma lem5438167 (_70508 : int) (_70505 : int) (_70507 : int) : (term384 _70508 _70505 _70507) = (term389 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438164 _70508) (@lem5438163 _70505 _70507)). Qed.
Lemma lem5438169 (_70508 : int) (_70505 : int) (_70507 : int) : (term383 _70508 _70505 _70507) = (term389 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5438120 _70508 _70505 _70507) (@lem5438167 _70508 _70505 _70507)). Qed.
Lemma lem5438170 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5438171 (_70508 : int) (_70505 : int) (_70507 : int) : (term390 _70508 _70505 _70507) = (term391 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438170) (@lem5438169 _70508 _70505 _70507)). Qed.
Lemma lem5438172 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5438173 (_70508 : int) (_70505 : int) (_70507 : int) : (term382 _70508 _70505 _70507) = (term392 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438171 _70508 _70505 _70507) (@lem5438172)). Qed.
Lemma lem5438174 (_70508 : int) (_70505 : int) (_70507 : int) : (term271 _70505 _70507 _70508) = (term392 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5438104 _70508 _70505 _70507) (@lem5438173 _70508 _70505 _70507)). Qed.
Lemma lem5438175 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5438176 (_70508 : int) (_70504 : int) (_70506 : int) : (term273 _70508 _70504 _70506) = (term393 _70508 _70504 _70506).
Proof. exact (MK_COMB (@lem5438175) (@lem5438103 _70508 _70504 _70506)). Qed.
Lemma lem5438177 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term274 _70504 _70506 _70505 _70507 _70508) = (term394 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438176 _70508 _70504 _70506) (@lem5438174 _70508 _70505 _70507)). Qed.
Lemma lem5438178 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5438179 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) : (term275 _70504 _70505 _70506 _70508 _70507) = (term395 _70504 _70505 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5438178) (@lem5438028 _70504 _70505 _70506 _70507 _70508)). Qed.
Lemma lem5438180 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term276 _70504 _70506 _70505 _70507 _70508) = (term396 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438179 _70504 _70505 _70506 _70507 _70508) (@lem5438177 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438181 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5438182 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term277 _70504 _70506 _70508 _70505 _70507) = (term397 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438181) (@lem5437943 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438183 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term278 _70504 _70506 _70505 _70507 _70508) = (term398 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438182 _70504 _70506 _70508 _70505 _70507) (@lem5438180 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438184 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5438185 (_70508 : int) : (term279 _70508) = (term399 _70508).
Proof. exact (MK_COMB (@lem5438184) (@lem5437606 _70508)). Qed.
Lemma lem5438186 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term280 _70504 _70506 _70505 _70507 _70508) = (term400 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438185 _70508) (@lem5438183 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438187 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5438188 (_70507 : int) : (term279 _70507) = (term399 _70507).
Proof. exact (MK_COMB (@lem5438187) (@lem5437558 _70507)). Qed.
Lemma lem5438189 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term281 _70504 _70506 _70505 _70507 _70508) = (term401 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438188 _70507) (@lem5438186 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438190 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5438191 (_70506 : int) : (term279 _70506) = (term399 _70506).
Proof. exact (MK_COMB (@lem5438190) (@lem5437510 _70506)). Qed.
Lemma lem5438192 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term282 _70504 _70506 _70505 _70507 _70508) = (term402 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438191 _70506) (@lem5438189 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438193 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5438194 (_70505 : int) : (term279 _70505) = (term399 _70505).
Proof. exact (MK_COMB (@lem5438193) (@lem5437462 _70505)). Qed.
Lemma lem5438195 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term283 _70504 _70506 _70505 _70507 _70508) = (term403 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438194 _70505) (@lem5438192 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5438197 (_70504 : int) : (term279 _70504) = (term399 _70504).
Proof. exact (MK_COMB (@lem5438196) (@lem5437414 _70504)). Qed.
Lemma lem5438198 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term284 _70504 _70506 _70505 _70507 _70508) = (term404 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438197 _70504) (@lem5438195 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438205 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term286 _70504 _70506 _70505 _70507 _70508) = (term404 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5437366 _70504 _70506 _70505 _70507 _70508) (@lem5438198 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438240 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term396 _70504 _70506 _70508 _70505 _70507) = (term405 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19158 (term381 _70508 _70504 _70506) (term372 _70504 _70505 _70506 _70507 _70508) (term392 _70508 _70505 _70507)). Qed.
Lemma lem5438264 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term359 _70504 _70506 _70508 _70505 _70507) = (term406 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19367 (term340 _70504 _70505 _70508) (term340 _70506 _70507 _70508) (term357 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438271 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term407 _70504 _70506 _70508 _70505 _70507) = (term408 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19367 (term334 _70506 _70508) (term338 _70507 _70508) (term357 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438278 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term409 _70504 _70506 _70508 _70505 _70507) = (term410 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19367 (term334 _70504 _70508) (term338 _70505 _70508) (term357 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438279 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5438280 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term411 _70504 _70506 _70508 _70505 _70507) = (term412 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438279) (@lem5438278 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438281 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term406 _70504 _70506 _70508 _70505 _70507) = (term413 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438280 _70504 _70506 _70508 _70505 _70507) (@lem5438271 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438283 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term359 _70504 _70506 _70508 _70505 _70507) = (term413 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5438264 _70504 _70506 _70508 _70505 _70507) (@lem5438281 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438284 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5438285 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term397 _70504 _70506 _70508 _70505 _70507) = (term414 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438284) (@lem5438283 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438286 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term398 _70504 _70506 _70508 _70505 _70507) = (term415 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438285 _70504 _70506 _70508 _70505 _70507) (@lem5438240 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438289 (_70508 : int) : (term399 _70508) = (term399 _70508).
Proof. exact (eq_refl (term399 _70508)). Qed.
Lemma lem5438290 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term400 _70504 _70506 _70508 _70505 _70507) = (term416 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438289 _70508) (@lem5438286 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438291 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term416 _70504 _70506 _70508 _70505 _70507) = (term417 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19158 (term413 _70504 _70506 _70508 _70505 _70507) (term314 _70508) (term405 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438298 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term418 _70504 _70506 _70508 _70505 _70507) = (term419 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19158 (term420 _70505 _70507 _70508 _70504 _70506) (term314 _70508) (term421 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438299 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term422 _70504 _70506 _70508 _70505 _70507) = (term423 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19158 (term410 _70504 _70506 _70508 _70505 _70507) (term314 _70508) (term408 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438306 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term424 _70504 _70506 _70508 _70505 _70507) = (term425 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19158 (term426 _70504 _70506 _70508 _70505 _70507) (term314 _70508) (term427 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438313 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term428 _70504 _70506 _70508 _70505 _70507) = (term429 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19158 (term430 _70504 _70506 _70508 _70505 _70507) (term314 _70508) (term431 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438314 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5438315 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term432 _70504 _70506 _70508 _70505 _70507) = (term433 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438314) (@lem5438313 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438316 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term423 _70504 _70506 _70508 _70505 _70507) = (term434 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438315 _70504 _70506 _70508 _70505 _70507) (@lem5438306 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438317 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term422 _70504 _70506 _70508 _70505 _70507) = (term434 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5438299 _70504 _70506 _70508 _70505 _70507) (@lem5438316 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438318 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5438319 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term435 _70504 _70506 _70508 _70505 _70507) = (term436 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438318) (@lem5438317 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438320 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term417 _70504 _70506 _70508 _70505 _70507) = (term437 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438319 _70504 _70506 _70508 _70505 _70507) (@lem5438298 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438321 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term416 _70504 _70506 _70508 _70505 _70507) = (term437 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5438291 _70504 _70506 _70508 _70505 _70507) (@lem5438320 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438322 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term400 _70504 _70506 _70508 _70505 _70507) = (term437 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5438290 _70504 _70506 _70508 _70505 _70507) (@lem5438321 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438325 (_70507 : int) : (term399 _70507) = (term399 _70507).
Proof. exact (eq_refl (term399 _70507)). Qed.
Lemma lem5438326 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term401 _70504 _70506 _70508 _70505 _70507) = (term438 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438325 _70507) (@lem5438322 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438327 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term438 _70504 _70506 _70508 _70505 _70507) = (term439 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19158 (term434 _70504 _70506 _70508 _70505 _70507) (term314 _70507) (term419 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438334 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term440 _70504 _70506 _70508 _70505 _70507) = (term441 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19158 (term442 _70505 _70507 _70508 _70504 _70506) (term314 _70507) (term443 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438335 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term444 _70504 _70506 _70508 _70505 _70507) = (term445 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19158 (term429 _70504 _70506 _70508 _70505 _70507) (term314 _70507) (term425 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438342 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term446 _70504 _70506 _70508 _70505 _70507) = (term447 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19158 (term448 _70504 _70506 _70508 _70505 _70507) (term314 _70507) (term449 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438349 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term450 _70504 _70506 _70508 _70505 _70507) = (term451 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19158 (term452 _70504 _70506 _70508 _70505 _70507) (term314 _70507) (term453 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438350 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5438351 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term454 _70504 _70506 _70508 _70505 _70507) = (term455 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438350) (@lem5438349 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438352 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term445 _70504 _70506 _70508 _70505 _70507) = (term456 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438351 _70504 _70506 _70508 _70505 _70507) (@lem5438342 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438353 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term444 _70504 _70506 _70508 _70505 _70507) = (term456 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5438335 _70504 _70506 _70508 _70505 _70507) (@lem5438352 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438354 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5438355 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term457 _70504 _70506 _70508 _70505 _70507) = (term458 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438354) (@lem5438353 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438356 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term439 _70504 _70506 _70508 _70505 _70507) = (term459 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438355 _70504 _70506 _70508 _70505 _70507) (@lem5438334 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438357 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term438 _70504 _70506 _70508 _70505 _70507) = (term459 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5438327 _70504 _70506 _70508 _70505 _70507) (@lem5438356 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438358 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term401 _70504 _70506 _70508 _70505 _70507) = (term459 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5438326 _70504 _70506 _70508 _70505 _70507) (@lem5438357 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438361 (_70506 : int) : (term399 _70506) = (term399 _70506).
Proof. exact (eq_refl (term399 _70506)). Qed.
Lemma lem5438362 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term402 _70504 _70506 _70508 _70505 _70507) = (term460 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438361 _70506) (@lem5438358 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438363 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term460 _70504 _70506 _70508 _70505 _70507) = (term461 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19158 (term456 _70504 _70506 _70508 _70505 _70507) (term314 _70506) (term441 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438370 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term462 _70504 _70506 _70508 _70505 _70507) = (term463 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19158 (term464 _70505 _70507 _70508 _70504 _70506) (term314 _70506) (term465 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438371 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term466 _70504 _70506 _70508 _70505 _70507) = (term467 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19158 (term451 _70504 _70506 _70508 _70505 _70507) (term314 _70506) (term447 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438378 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term468 _70504 _70506 _70508 _70505 _70507) = (term469 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19158 (term470 _70504 _70506 _70508 _70505 _70507) (term314 _70506) (term471 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438385 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term472 _70504 _70506 _70508 _70505 _70507) = (term473 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19158 (term474 _70504 _70506 _70508 _70505 _70507) (term314 _70506) (term475 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438386 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5438387 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term476 _70504 _70506 _70508 _70505 _70507) = (term477 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438386) (@lem5438385 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438388 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term467 _70504 _70506 _70508 _70505 _70507) = (term478 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438387 _70504 _70506 _70508 _70505 _70507) (@lem5438378 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438389 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term466 _70504 _70506 _70508 _70505 _70507) = (term478 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5438371 _70504 _70506 _70508 _70505 _70507) (@lem5438388 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438390 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5438391 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term479 _70504 _70506 _70508 _70505 _70507) = (term480 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438390) (@lem5438389 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438392 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term461 _70504 _70506 _70508 _70505 _70507) = (term481 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438391 _70504 _70506 _70508 _70505 _70507) (@lem5438370 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438393 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term460 _70504 _70506 _70508 _70505 _70507) = (term481 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5438363 _70504 _70506 _70508 _70505 _70507) (@lem5438392 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438394 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term402 _70504 _70506 _70508 _70505 _70507) = (term481 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5438362 _70504 _70506 _70508 _70505 _70507) (@lem5438393 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438397 (_70505 : int) : (term399 _70505) = (term399 _70505).
Proof. exact (eq_refl (term399 _70505)). Qed.
Lemma lem5438398 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term403 _70504 _70506 _70508 _70505 _70507) = (term482 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438397 _70505) (@lem5438394 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438399 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term482 _70504 _70506 _70508 _70505 _70507) = (term483 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19158 (term478 _70504 _70506 _70508 _70505 _70507) (term314 _70505) (term463 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438406 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term484 _70504 _70506 _70508 _70505 _70507) = (term485 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19158 (term486 _70505 _70507 _70508 _70504 _70506) (term314 _70505) (term487 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438407 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term488 _70504 _70506 _70508 _70505 _70507) = (term489 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19158 (term473 _70504 _70506 _70508 _70505 _70507) (term314 _70505) (term469 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438414 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term490 _70504 _70506 _70508 _70505 _70507) = (term491 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19158 (term492 _70504 _70506 _70508 _70505 _70507) (term314 _70505) (term493 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438421 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term494 _70504 _70506 _70508 _70505 _70507) = (term495 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19158 (term496 _70504 _70506 _70508 _70505 _70507) (term314 _70505) (term497 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438422 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5438423 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term498 _70504 _70506 _70508 _70505 _70507) = (term499 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438422) (@lem5438421 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438424 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term489 _70504 _70506 _70508 _70505 _70507) = (term500 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438423 _70504 _70506 _70508 _70505 _70507) (@lem5438414 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438425 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term488 _70504 _70506 _70508 _70505 _70507) = (term500 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5438407 _70504 _70506 _70508 _70505 _70507) (@lem5438424 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438426 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5438427 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term501 _70504 _70506 _70508 _70505 _70507) = (term502 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438426) (@lem5438425 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438428 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term483 _70504 _70506 _70508 _70505 _70507) = (term503 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438427 _70504 _70506 _70508 _70505 _70507) (@lem5438406 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438429 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term482 _70504 _70506 _70508 _70505 _70507) = (term503 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5438399 _70504 _70506 _70508 _70505 _70507) (@lem5438428 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438430 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term403 _70504 _70506 _70508 _70505 _70507) = (term503 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5438398 _70504 _70506 _70508 _70505 _70507) (@lem5438429 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438433 (_70504 : int) : (term399 _70504) = (term399 _70504).
Proof. exact (eq_refl (term399 _70504)). Qed.
Lemma lem5438434 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term404 _70504 _70506 _70508 _70505 _70507) = (term504 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438433 _70504) (@lem5438430 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438435 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term504 _70504 _70506 _70508 _70505 _70507) = (term505 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19158 (term500 _70504 _70506 _70508 _70505 _70507) (term314 _70504) (term485 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438442 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term506 _70504 _70506 _70508 _70505 _70507) = (term507 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19158 (term508 _70505 _70507 _70508 _70504 _70506) (term314 _70504) (term509 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438443 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term510 _70504 _70506 _70508 _70505 _70507) = (term511 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19158 (term495 _70504 _70506 _70508 _70505 _70507) (term314 _70504) (term491 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438450 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term512 _70504 _70506 _70508 _70505 _70507) = (term513 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19158 (term514 _70504 _70506 _70508 _70505 _70507) (term314 _70504) (term515 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438457 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term516 _70504 _70506 _70508 _70505 _70507) = (term517 _70504 _70506 _70508 _70505 _70507).
Proof. exact (@lem19158 (term518 _70504 _70506 _70508 _70505 _70507) (term314 _70504) (term519 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438458 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5438459 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term520 _70504 _70506 _70508 _70505 _70507) = (term521 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438458) (@lem5438457 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438460 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term511 _70504 _70506 _70508 _70505 _70507) = (term522 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438459 _70504 _70506 _70508 _70505 _70507) (@lem5438450 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438461 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term510 _70504 _70506 _70508 _70505 _70507) = (term522 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5438443 _70504 _70506 _70508 _70505 _70507) (@lem5438460 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438462 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5438463 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term523 _70504 _70506 _70508 _70505 _70507) = (term524 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438462) (@lem5438461 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438464 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term505 _70504 _70506 _70508 _70505 _70507) = (term525 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5438463 _70504 _70506 _70508 _70505 _70507) (@lem5438442 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438465 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term504 _70504 _70506 _70508 _70505 _70507) = (term525 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5438435 _70504 _70506 _70508 _70505 _70507) (@lem5438464 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438466 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term404 _70504 _70506 _70508 _70505 _70507) = (term525 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5438434 _70504 _70506 _70508 _70505 _70507) (@lem5438465 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438467 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term286 _70504 _70506 _70505 _70507 _70508) = (term525 _70504 _70506 _70508 _70505 _70507).
Proof. exact (TRANS (@lem5438205 _70504 _70506 _70508 _70505 _70507) (@lem5438466 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5438469 (x : real) (a : real) (y : real) (r : real) : (term526 a x y r) = (term527 x a y r).
Proof. exact (proj1 (@lem1482686 x a (@el real) y (@el real) r)). Qed.
Lemma lem5438470 (_70504 : int) (_70508 : int) (_70506 : int) : (term348 _70508 _70504 _70506) = (term528 _70504 _70508 _70506).
Proof. exact (@lem5438469 (real_of_int _70504) (real_of_int _70508) (real_of_int _70506) term214). Qed.
Lemma lem5438483 (_70506 : int) (_70508 : int) : (term362 _70508 _70506) = (term363 _70506 _70508).
Proof. exact (@lem1982761 (term336 _70506) (real_of_int _70508)). Qed.
Lemma lem5438484 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5438485 (_70506 : int) (_70508 : int) : (term367 _70508 _70506) = (term365 _70506 _70508).
Proof. exact (MK_COMB (@lem5438484) (@lem5438483 _70506 _70508)). Qed.
Lemma lem5438486 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5438487 (_70506 : int) (_70508 : int) : (term368 _70508 _70506) = (term366 _70506 _70508).
Proof. exact (MK_COMB (@lem5438485 _70506 _70508) (@lem5438486)). Qed.
Lemma lem5438500 (_70504 : int) (_70508 : int) : (term362 _70508 _70504) = (term363 _70504 _70508).
Proof. exact (@lem1982761 (term336 _70504) (real_of_int _70508)). Qed.
Lemma lem5438501 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5438502 (_70504 : int) (_70508 : int) : (term367 _70508 _70504) = (term365 _70504 _70508).
Proof. exact (MK_COMB (@lem5438501) (@lem5438500 _70504 _70508)). Qed.
Lemma lem5438503 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5438504 (_70504 : int) (_70508 : int) : (term368 _70508 _70504) = (term366 _70504 _70508).
Proof. exact (MK_COMB (@lem5438502 _70504 _70508) (@lem5438503)). Qed.
Lemma lem5438505 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5438506 (_70504 : int) (_70508 : int) : (term529 _70508 _70504) = (term369 _70504 _70508).
Proof. exact (MK_COMB (@lem5438505) (@lem5438504 _70504 _70508)). Qed.
Lemma lem5438507 (_70504 : int) (_70506 : int) (_70508 : int) : (term528 _70504 _70508 _70506) = (term530 _70504 _70506 _70508).
Proof. exact (MK_COMB (@lem5438506 _70504 _70508) (@lem5438487 _70506 _70508)). Qed.
Lemma lem5438508 (_70504 : int) (_70506 : int) (_70508 : int) : (term348 _70508 _70504 _70506) = (term530 _70504 _70506 _70508).
Proof. exact (TRANS (@lem5438470 _70504 _70508 _70506) (@lem5438507 _70504 _70506 _70508)). Qed.
Lemma lem5438509 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5438510 (_70504 : int) (_70506 : int) (_70508 : int) : (term356 _70508 _70504 _70506) = (term531 _70504 _70506 _70508).
Proof. exact (MK_COMB (@lem5438509) (@lem5438508 _70504 _70506 _70508)). Qed.
Lemma lem5438512 (x : real) (a : real) (y : real) (r : real) : (term532 a x y r) = (term533 x a y r).
Proof. exact (proj1 (@lem1482698 x a (@el real) y (@el real) r)). Qed.
Lemma lem5438513 (_70505 : int) (_70508 : int) (_70507 : int) : (term355 _70508 _70505 _70507) = (term534 _70505 _70508 _70507).
Proof. exact (@lem5438512 (real_of_int _70505) (term336 _70508) (real_of_int _70507) term214). Qed.
Lemma lem5438526 (_70507 : int) (_70508 : int) : (term363 _70508 _70507) = (term362 _70507 _70508).
Proof. exact (@lem1982761 (real_of_int _70507) (term336 _70508)). Qed.
Lemma lem5438527 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5438528 (_70507 : int) (_70508 : int) : (term365 _70508 _70507) = (term367 _70507 _70508).
Proof. exact (MK_COMB (@lem5438527) (@lem5438526 _70507 _70508)). Qed.
Lemma lem5438529 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5438530 (_70507 : int) (_70508 : int) : (term366 _70508 _70507) = (term368 _70507 _70508).
Proof. exact (MK_COMB (@lem5438528 _70507 _70508) (@lem5438529)). Qed.
Lemma lem5438543 (_70505 : int) (_70508 : int) : (term363 _70508 _70505) = (term362 _70505 _70508).
Proof. exact (@lem1982761 (real_of_int _70505) (term336 _70508)). Qed.
Lemma lem5438544 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5438545 (_70505 : int) (_70508 : int) : (term365 _70508 _70505) = (term367 _70505 _70508).
Proof. exact (MK_COMB (@lem5438544) (@lem5438543 _70505 _70508)). Qed.
Lemma lem5438546 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5438547 (_70505 : int) (_70508 : int) : (term366 _70508 _70505) = (term368 _70505 _70508).
Proof. exact (MK_COMB (@lem5438545 _70505 _70508) (@lem5438546)). Qed.
Lemma lem5438548 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5438549 (_70505 : int) (_70508 : int) : (term369 _70508 _70505) = (term529 _70505 _70508).
Proof. exact (MK_COMB (@lem5438548) (@lem5438547 _70505 _70508)). Qed.
Lemma lem5438550 (_70505 : int) (_70507 : int) (_70508 : int) : (term534 _70505 _70508 _70507) = (term535 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438549 _70505 _70508) (@lem5438530 _70507 _70508)). Qed.
Lemma lem5438551 (_70505 : int) (_70507 : int) (_70508 : int) : (term355 _70508 _70505 _70507) = (term535 _70505 _70507 _70508).
Proof. exact (TRANS (@lem5438513 _70505 _70508 _70507) (@lem5438550 _70505 _70507 _70508)). Qed.
Lemma lem5438552 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term357 _70504 _70506 _70508 _70505 _70507) = (term536 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438510 _70504 _70506 _70508) (@lem5438551 _70505 _70507 _70508)). Qed.
Lemma lem5438553 (_70504 : int) (_70508 : int) : (term537 _70504 _70508) = (term537 _70504 _70508).
Proof. exact (eq_refl (term537 _70504 _70508)). Qed.
Lemma lem5438554 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term430 _70504 _70506 _70508 _70505 _70507) = (term538 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438553 _70504 _70508) (@lem5438552 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438555 (_70508 : int) : (term399 _70508) = (term399 _70508).
Proof. exact (eq_refl (term399 _70508)). Qed.
Lemma lem5438556 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term452 _70504 _70506 _70508 _70505 _70507) = (term539 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438555 _70508) (@lem5438554 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438557 (_70507 : int) : (term399 _70507) = (term399 _70507).
Proof. exact (eq_refl (term399 _70507)). Qed.
Lemma lem5438558 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term474 _70504 _70506 _70508 _70505 _70507) = (term540 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438557 _70507) (@lem5438556 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438559 (_70506 : int) : (term399 _70506) = (term399 _70506).
Proof. exact (eq_refl (term399 _70506)). Qed.
Lemma lem5438560 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term496 _70504 _70506 _70508 _70505 _70507) = (term541 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438559 _70506) (@lem5438558 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438561 (_70505 : int) : (term399 _70505) = (term399 _70505).
Proof. exact (eq_refl (term399 _70505)). Qed.
Lemma lem5438562 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term518 _70504 _70506 _70508 _70505 _70507) = (term542 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438561 _70505) (@lem5438560 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438563 (_70504 : int) : (term399 _70504) = (term399 _70504).
Proof. exact (eq_refl (term399 _70504)). Qed.
Lemma lem5438566 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term543 _70504 _70506 _70508 _70505 _70507) = (term544 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438563 _70504) (@lem5438562 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438568 (x : real) (a : real) (y : real) (r : real) : (term526 a x y r) = (term527 x a y r).
Proof. exact (proj1 (@lem1482686 x a (@el real) y (@el real) r)). Qed.
Lemma lem5438569 (_70504 : int) (_70508 : int) (_70506 : int) : (term348 _70508 _70504 _70506) = (term528 _70504 _70508 _70506).
Proof. exact (@lem5438568 (real_of_int _70504) (real_of_int _70508) (real_of_int _70506) term214). Qed.
Lemma lem5438582 (_70506 : int) (_70508 : int) : (term362 _70508 _70506) = (term363 _70506 _70508).
Proof. exact (@lem1982761 (term336 _70506) (real_of_int _70508)). Qed.
Lemma lem5438583 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5438584 (_70506 : int) (_70508 : int) : (term367 _70508 _70506) = (term365 _70506 _70508).
Proof. exact (MK_COMB (@lem5438583) (@lem5438582 _70506 _70508)). Qed.
Lemma lem5438585 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5438586 (_70506 : int) (_70508 : int) : (term368 _70508 _70506) = (term366 _70506 _70508).
Proof. exact (MK_COMB (@lem5438584 _70506 _70508) (@lem5438585)). Qed.
Lemma lem5438599 (_70504 : int) (_70508 : int) : (term362 _70508 _70504) = (term363 _70504 _70508).
Proof. exact (@lem1982761 (term336 _70504) (real_of_int _70508)). Qed.
Lemma lem5438600 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5438601 (_70504 : int) (_70508 : int) : (term367 _70508 _70504) = (term365 _70504 _70508).
Proof. exact (MK_COMB (@lem5438600) (@lem5438599 _70504 _70508)). Qed.
Lemma lem5438602 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5438603 (_70504 : int) (_70508 : int) : (term368 _70508 _70504) = (term366 _70504 _70508).
Proof. exact (MK_COMB (@lem5438601 _70504 _70508) (@lem5438602)). Qed.
Lemma lem5438604 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5438605 (_70504 : int) (_70508 : int) : (term529 _70508 _70504) = (term369 _70504 _70508).
Proof. exact (MK_COMB (@lem5438604) (@lem5438603 _70504 _70508)). Qed.
Lemma lem5438606 (_70504 : int) (_70506 : int) (_70508 : int) : (term528 _70504 _70508 _70506) = (term530 _70504 _70506 _70508).
Proof. exact (MK_COMB (@lem5438605 _70504 _70508) (@lem5438586 _70506 _70508)). Qed.
Lemma lem5438607 (_70504 : int) (_70506 : int) (_70508 : int) : (term348 _70508 _70504 _70506) = (term530 _70504 _70506 _70508).
Proof. exact (TRANS (@lem5438569 _70504 _70508 _70506) (@lem5438606 _70504 _70506 _70508)). Qed.
Lemma lem5438608 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5438609 (_70504 : int) (_70506 : int) (_70508 : int) : (term356 _70508 _70504 _70506) = (term531 _70504 _70506 _70508).
Proof. exact (MK_COMB (@lem5438608) (@lem5438607 _70504 _70506 _70508)). Qed.
Lemma lem5438611 (x : real) (a : real) (y : real) (r : real) : (term532 a x y r) = (term533 x a y r).
Proof. exact (proj1 (@lem1482698 x a (@el real) y (@el real) r)). Qed.
Lemma lem5438612 (_70505 : int) (_70508 : int) (_70507 : int) : (term355 _70508 _70505 _70507) = (term534 _70505 _70508 _70507).
Proof. exact (@lem5438611 (real_of_int _70505) (term336 _70508) (real_of_int _70507) term214). Qed.
Lemma lem5438625 (_70507 : int) (_70508 : int) : (term363 _70508 _70507) = (term362 _70507 _70508).
Proof. exact (@lem1982761 (real_of_int _70507) (term336 _70508)). Qed.
Lemma lem5438626 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5438627 (_70507 : int) (_70508 : int) : (term365 _70508 _70507) = (term367 _70507 _70508).
Proof. exact (MK_COMB (@lem5438626) (@lem5438625 _70507 _70508)). Qed.
Lemma lem5438628 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5438629 (_70507 : int) (_70508 : int) : (term366 _70508 _70507) = (term368 _70507 _70508).
Proof. exact (MK_COMB (@lem5438627 _70507 _70508) (@lem5438628)). Qed.
Lemma lem5438642 (_70505 : int) (_70508 : int) : (term363 _70508 _70505) = (term362 _70505 _70508).
Proof. exact (@lem1982761 (real_of_int _70505) (term336 _70508)). Qed.
Lemma lem5438643 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5438644 (_70505 : int) (_70508 : int) : (term365 _70508 _70505) = (term367 _70505 _70508).
Proof. exact (MK_COMB (@lem5438643) (@lem5438642 _70505 _70508)). Qed.
Lemma lem5438645 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5438646 (_70505 : int) (_70508 : int) : (term366 _70508 _70505) = (term368 _70505 _70508).
Proof. exact (MK_COMB (@lem5438644 _70505 _70508) (@lem5438645)). Qed.
Lemma lem5438647 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5438648 (_70505 : int) (_70508 : int) : (term369 _70508 _70505) = (term529 _70505 _70508).
Proof. exact (MK_COMB (@lem5438647) (@lem5438646 _70505 _70508)). Qed.
Lemma lem5438649 (_70505 : int) (_70507 : int) (_70508 : int) : (term534 _70505 _70508 _70507) = (term535 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438648 _70505 _70508) (@lem5438629 _70507 _70508)). Qed.
Lemma lem5438650 (_70505 : int) (_70507 : int) (_70508 : int) : (term355 _70508 _70505 _70507) = (term535 _70505 _70507 _70508).
Proof. exact (TRANS (@lem5438612 _70505 _70508 _70507) (@lem5438649 _70505 _70507 _70508)). Qed.
Lemma lem5438651 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term357 _70504 _70506 _70508 _70505 _70507) = (term536 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438609 _70504 _70506 _70508) (@lem5438650 _70505 _70507 _70508)). Qed.
Lemma lem5438652 (_70505 : int) (_70508 : int) : (term545 _70505 _70508) = (term545 _70505 _70508).
Proof. exact (eq_refl (term545 _70505 _70508)). Qed.
Lemma lem5438653 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term431 _70504 _70506 _70508 _70505 _70507) = (term546 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438652 _70505 _70508) (@lem5438651 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438654 (_70508 : int) : (term399 _70508) = (term399 _70508).
Proof. exact (eq_refl (term399 _70508)). Qed.
Lemma lem5438655 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term453 _70504 _70506 _70508 _70505 _70507) = (term547 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438654 _70508) (@lem5438653 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438656 (_70507 : int) : (term399 _70507) = (term399 _70507).
Proof. exact (eq_refl (term399 _70507)). Qed.
Lemma lem5438657 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term475 _70504 _70506 _70508 _70505 _70507) = (term548 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438656 _70507) (@lem5438655 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438658 (_70506 : int) : (term399 _70506) = (term399 _70506).
Proof. exact (eq_refl (term399 _70506)). Qed.
Lemma lem5438659 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term497 _70504 _70506 _70508 _70505 _70507) = (term549 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438658 _70506) (@lem5438657 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438660 (_70505 : int) : (term399 _70505) = (term399 _70505).
Proof. exact (eq_refl (term399 _70505)). Qed.
Lemma lem5438661 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term519 _70504 _70506 _70508 _70505 _70507) = (term550 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438660 _70505) (@lem5438659 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438662 (_70504 : int) : (term399 _70504) = (term399 _70504).
Proof. exact (eq_refl (term399 _70504)). Qed.
Lemma lem5438665 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term551 _70504 _70506 _70508 _70505 _70507) = (term552 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438662 _70504) (@lem5438661 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438666 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5438667 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term553 _70504 _70506 _70508 _70505 _70507) = (term554 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438666) (@lem5438566 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438668 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term517 _70504 _70506 _70508 _70505 _70507) = (term555 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438667 _70504 _70506 _70505 _70507 _70508) (@lem5438665 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438670 (x : real) (a : real) (y : real) (r : real) : (term526 a x y r) = (term527 x a y r).
Proof. exact (proj1 (@lem1482686 x a (@el real) y (@el real) r)). Qed.
Lemma lem5438671 (_70504 : int) (_70508 : int) (_70506 : int) : (term348 _70508 _70504 _70506) = (term528 _70504 _70508 _70506).
Proof. exact (@lem5438670 (real_of_int _70504) (real_of_int _70508) (real_of_int _70506) term214). Qed.
Lemma lem5438684 (_70506 : int) (_70508 : int) : (term362 _70508 _70506) = (term363 _70506 _70508).
Proof. exact (@lem1982761 (term336 _70506) (real_of_int _70508)). Qed.
Lemma lem5438685 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5438686 (_70506 : int) (_70508 : int) : (term367 _70508 _70506) = (term365 _70506 _70508).
Proof. exact (MK_COMB (@lem5438685) (@lem5438684 _70506 _70508)). Qed.
Lemma lem5438687 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5438688 (_70506 : int) (_70508 : int) : (term368 _70508 _70506) = (term366 _70506 _70508).
Proof. exact (MK_COMB (@lem5438686 _70506 _70508) (@lem5438687)). Qed.
Lemma lem5438701 (_70504 : int) (_70508 : int) : (term362 _70508 _70504) = (term363 _70504 _70508).
Proof. exact (@lem1982761 (term336 _70504) (real_of_int _70508)). Qed.
Lemma lem5438702 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5438703 (_70504 : int) (_70508 : int) : (term367 _70508 _70504) = (term365 _70504 _70508).
Proof. exact (MK_COMB (@lem5438702) (@lem5438701 _70504 _70508)). Qed.
Lemma lem5438704 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5438705 (_70504 : int) (_70508 : int) : (term368 _70508 _70504) = (term366 _70504 _70508).
Proof. exact (MK_COMB (@lem5438703 _70504 _70508) (@lem5438704)). Qed.
Lemma lem5438706 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5438707 (_70504 : int) (_70508 : int) : (term529 _70508 _70504) = (term369 _70504 _70508).
Proof. exact (MK_COMB (@lem5438706) (@lem5438705 _70504 _70508)). Qed.
Lemma lem5438708 (_70504 : int) (_70506 : int) (_70508 : int) : (term528 _70504 _70508 _70506) = (term530 _70504 _70506 _70508).
Proof. exact (MK_COMB (@lem5438707 _70504 _70508) (@lem5438688 _70506 _70508)). Qed.
Lemma lem5438709 (_70504 : int) (_70506 : int) (_70508 : int) : (term348 _70508 _70504 _70506) = (term530 _70504 _70506 _70508).
Proof. exact (TRANS (@lem5438671 _70504 _70508 _70506) (@lem5438708 _70504 _70506 _70508)). Qed.
Lemma lem5438710 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5438711 (_70504 : int) (_70506 : int) (_70508 : int) : (term356 _70508 _70504 _70506) = (term531 _70504 _70506 _70508).
Proof. exact (MK_COMB (@lem5438710) (@lem5438709 _70504 _70506 _70508)). Qed.
Lemma lem5438713 (x : real) (a : real) (y : real) (r : real) : (term532 a x y r) = (term533 x a y r).
Proof. exact (proj1 (@lem1482698 x a (@el real) y (@el real) r)). Qed.
Lemma lem5438714 (_70505 : int) (_70508 : int) (_70507 : int) : (term355 _70508 _70505 _70507) = (term534 _70505 _70508 _70507).
Proof. exact (@lem5438713 (real_of_int _70505) (term336 _70508) (real_of_int _70507) term214). Qed.
Lemma lem5438727 (_70507 : int) (_70508 : int) : (term363 _70508 _70507) = (term362 _70507 _70508).
Proof. exact (@lem1982761 (real_of_int _70507) (term336 _70508)). Qed.
Lemma lem5438728 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5438729 (_70507 : int) (_70508 : int) : (term365 _70508 _70507) = (term367 _70507 _70508).
Proof. exact (MK_COMB (@lem5438728) (@lem5438727 _70507 _70508)). Qed.
Lemma lem5438730 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5438731 (_70507 : int) (_70508 : int) : (term366 _70508 _70507) = (term368 _70507 _70508).
Proof. exact (MK_COMB (@lem5438729 _70507 _70508) (@lem5438730)). Qed.
Lemma lem5438744 (_70505 : int) (_70508 : int) : (term363 _70508 _70505) = (term362 _70505 _70508).
Proof. exact (@lem1982761 (real_of_int _70505) (term336 _70508)). Qed.
Lemma lem5438745 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5438746 (_70505 : int) (_70508 : int) : (term365 _70508 _70505) = (term367 _70505 _70508).
Proof. exact (MK_COMB (@lem5438745) (@lem5438744 _70505 _70508)). Qed.
Lemma lem5438747 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5438748 (_70505 : int) (_70508 : int) : (term366 _70508 _70505) = (term368 _70505 _70508).
Proof. exact (MK_COMB (@lem5438746 _70505 _70508) (@lem5438747)). Qed.
Lemma lem5438749 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5438750 (_70505 : int) (_70508 : int) : (term369 _70508 _70505) = (term529 _70505 _70508).
Proof. exact (MK_COMB (@lem5438749) (@lem5438748 _70505 _70508)). Qed.
Lemma lem5438751 (_70505 : int) (_70507 : int) (_70508 : int) : (term534 _70505 _70508 _70507) = (term535 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438750 _70505 _70508) (@lem5438731 _70507 _70508)). Qed.
Lemma lem5438752 (_70505 : int) (_70507 : int) (_70508 : int) : (term355 _70508 _70505 _70507) = (term535 _70505 _70507 _70508).
Proof. exact (TRANS (@lem5438714 _70505 _70508 _70507) (@lem5438751 _70505 _70507 _70508)). Qed.
Lemma lem5438753 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term357 _70504 _70506 _70508 _70505 _70507) = (term536 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438711 _70504 _70506 _70508) (@lem5438752 _70505 _70507 _70508)). Qed.
Lemma lem5438754 (_70506 : int) (_70508 : int) : (term537 _70506 _70508) = (term537 _70506 _70508).
Proof. exact (eq_refl (term537 _70506 _70508)). Qed.
Lemma lem5438755 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term426 _70504 _70506 _70508 _70505 _70507) = (term556 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438754 _70506 _70508) (@lem5438753 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438756 (_70508 : int) : (term399 _70508) = (term399 _70508).
Proof. exact (eq_refl (term399 _70508)). Qed.
Lemma lem5438757 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term448 _70504 _70506 _70508 _70505 _70507) = (term557 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438756 _70508) (@lem5438755 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438758 (_70507 : int) : (term399 _70507) = (term399 _70507).
Proof. exact (eq_refl (term399 _70507)). Qed.
Lemma lem5438759 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term470 _70504 _70506 _70508 _70505 _70507) = (term558 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438758 _70507) (@lem5438757 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438760 (_70506 : int) : (term399 _70506) = (term399 _70506).
Proof. exact (eq_refl (term399 _70506)). Qed.
Lemma lem5438761 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term492 _70504 _70506 _70508 _70505 _70507) = (term559 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438760 _70506) (@lem5438759 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438762 (_70505 : int) : (term399 _70505) = (term399 _70505).
Proof. exact (eq_refl (term399 _70505)). Qed.
Lemma lem5438763 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term514 _70504 _70506 _70508 _70505 _70507) = (term560 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438762 _70505) (@lem5438761 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438764 (_70504 : int) : (term399 _70504) = (term399 _70504).
Proof. exact (eq_refl (term399 _70504)). Qed.
Lemma lem5438767 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term561 _70504 _70506 _70508 _70505 _70507) = (term562 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438764 _70504) (@lem5438763 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438769 (x : real) (a : real) (y : real) (r : real) : (term526 a x y r) = (term527 x a y r).
Proof. exact (proj1 (@lem1482686 x a (@el real) y (@el real) r)). Qed.
Lemma lem5438770 (_70504 : int) (_70508 : int) (_70506 : int) : (term348 _70508 _70504 _70506) = (term528 _70504 _70508 _70506).
Proof. exact (@lem5438769 (real_of_int _70504) (real_of_int _70508) (real_of_int _70506) term214). Qed.
Lemma lem5438783 (_70506 : int) (_70508 : int) : (term362 _70508 _70506) = (term363 _70506 _70508).
Proof. exact (@lem1982761 (term336 _70506) (real_of_int _70508)). Qed.
Lemma lem5438784 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5438785 (_70506 : int) (_70508 : int) : (term367 _70508 _70506) = (term365 _70506 _70508).
Proof. exact (MK_COMB (@lem5438784) (@lem5438783 _70506 _70508)). Qed.
Lemma lem5438786 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5438787 (_70506 : int) (_70508 : int) : (term368 _70508 _70506) = (term366 _70506 _70508).
Proof. exact (MK_COMB (@lem5438785 _70506 _70508) (@lem5438786)). Qed.
Lemma lem5438800 (_70504 : int) (_70508 : int) : (term362 _70508 _70504) = (term363 _70504 _70508).
Proof. exact (@lem1982761 (term336 _70504) (real_of_int _70508)). Qed.
Lemma lem5438801 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5438802 (_70504 : int) (_70508 : int) : (term367 _70508 _70504) = (term365 _70504 _70508).
Proof. exact (MK_COMB (@lem5438801) (@lem5438800 _70504 _70508)). Qed.
Lemma lem5438803 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5438804 (_70504 : int) (_70508 : int) : (term368 _70508 _70504) = (term366 _70504 _70508).
Proof. exact (MK_COMB (@lem5438802 _70504 _70508) (@lem5438803)). Qed.
Lemma lem5438805 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5438806 (_70504 : int) (_70508 : int) : (term529 _70508 _70504) = (term369 _70504 _70508).
Proof. exact (MK_COMB (@lem5438805) (@lem5438804 _70504 _70508)). Qed.
Lemma lem5438807 (_70504 : int) (_70506 : int) (_70508 : int) : (term528 _70504 _70508 _70506) = (term530 _70504 _70506 _70508).
Proof. exact (MK_COMB (@lem5438806 _70504 _70508) (@lem5438787 _70506 _70508)). Qed.
Lemma lem5438808 (_70504 : int) (_70506 : int) (_70508 : int) : (term348 _70508 _70504 _70506) = (term530 _70504 _70506 _70508).
Proof. exact (TRANS (@lem5438770 _70504 _70508 _70506) (@lem5438807 _70504 _70506 _70508)). Qed.
Lemma lem5438809 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5438810 (_70504 : int) (_70506 : int) (_70508 : int) : (term356 _70508 _70504 _70506) = (term531 _70504 _70506 _70508).
Proof. exact (MK_COMB (@lem5438809) (@lem5438808 _70504 _70506 _70508)). Qed.
Lemma lem5438812 (x : real) (a : real) (y : real) (r : real) : (term532 a x y r) = (term533 x a y r).
Proof. exact (proj1 (@lem1482698 x a (@el real) y (@el real) r)). Qed.
Lemma lem5438813 (_70505 : int) (_70508 : int) (_70507 : int) : (term355 _70508 _70505 _70507) = (term534 _70505 _70508 _70507).
Proof. exact (@lem5438812 (real_of_int _70505) (term336 _70508) (real_of_int _70507) term214). Qed.
Lemma lem5438826 (_70507 : int) (_70508 : int) : (term363 _70508 _70507) = (term362 _70507 _70508).
Proof. exact (@lem1982761 (real_of_int _70507) (term336 _70508)). Qed.
Lemma lem5438827 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5438828 (_70507 : int) (_70508 : int) : (term365 _70508 _70507) = (term367 _70507 _70508).
Proof. exact (MK_COMB (@lem5438827) (@lem5438826 _70507 _70508)). Qed.
Lemma lem5438829 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5438830 (_70507 : int) (_70508 : int) : (term366 _70508 _70507) = (term368 _70507 _70508).
Proof. exact (MK_COMB (@lem5438828 _70507 _70508) (@lem5438829)). Qed.
Lemma lem5438843 (_70505 : int) (_70508 : int) : (term363 _70508 _70505) = (term362 _70505 _70508).
Proof. exact (@lem1982761 (real_of_int _70505) (term336 _70508)). Qed.
Lemma lem5438844 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5438845 (_70505 : int) (_70508 : int) : (term365 _70508 _70505) = (term367 _70505 _70508).
Proof. exact (MK_COMB (@lem5438844) (@lem5438843 _70505 _70508)). Qed.
Lemma lem5438846 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5438847 (_70505 : int) (_70508 : int) : (term366 _70508 _70505) = (term368 _70505 _70508).
Proof. exact (MK_COMB (@lem5438845 _70505 _70508) (@lem5438846)). Qed.
Lemma lem5438848 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5438849 (_70505 : int) (_70508 : int) : (term369 _70508 _70505) = (term529 _70505 _70508).
Proof. exact (MK_COMB (@lem5438848) (@lem5438847 _70505 _70508)). Qed.
Lemma lem5438850 (_70505 : int) (_70507 : int) (_70508 : int) : (term534 _70505 _70508 _70507) = (term535 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438849 _70505 _70508) (@lem5438830 _70507 _70508)). Qed.
Lemma lem5438851 (_70505 : int) (_70507 : int) (_70508 : int) : (term355 _70508 _70505 _70507) = (term535 _70505 _70507 _70508).
Proof. exact (TRANS (@lem5438813 _70505 _70508 _70507) (@lem5438850 _70505 _70507 _70508)). Qed.
Lemma lem5438852 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term357 _70504 _70506 _70508 _70505 _70507) = (term536 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438810 _70504 _70506 _70508) (@lem5438851 _70505 _70507 _70508)). Qed.
Lemma lem5438853 (_70507 : int) (_70508 : int) : (term545 _70507 _70508) = (term545 _70507 _70508).
Proof. exact (eq_refl (term545 _70507 _70508)). Qed.
Lemma lem5438854 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term427 _70504 _70506 _70508 _70505 _70507) = (term563 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438853 _70507 _70508) (@lem5438852 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438855 (_70508 : int) : (term399 _70508) = (term399 _70508).
Proof. exact (eq_refl (term399 _70508)). Qed.
Lemma lem5438856 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term449 _70504 _70506 _70508 _70505 _70507) = (term564 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438855 _70508) (@lem5438854 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438857 (_70507 : int) : (term399 _70507) = (term399 _70507).
Proof. exact (eq_refl (term399 _70507)). Qed.
Lemma lem5438858 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term471 _70504 _70506 _70508 _70505 _70507) = (term565 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438857 _70507) (@lem5438856 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438859 (_70506 : int) : (term399 _70506) = (term399 _70506).
Proof. exact (eq_refl (term399 _70506)). Qed.
Lemma lem5438860 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term493 _70504 _70506 _70508 _70505 _70507) = (term566 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438859 _70506) (@lem5438858 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438861 (_70505 : int) : (term399 _70505) = (term399 _70505).
Proof. exact (eq_refl (term399 _70505)). Qed.
Lemma lem5438862 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term515 _70504 _70506 _70508 _70505 _70507) = (term567 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438861 _70505) (@lem5438860 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438863 (_70504 : int) : (term399 _70504) = (term399 _70504).
Proof. exact (eq_refl (term399 _70504)). Qed.
Lemma lem5438866 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term568 _70504 _70506 _70508 _70505 _70507) = (term569 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438863 _70504) (@lem5438862 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438867 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5438868 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term570 _70504 _70506 _70508 _70505 _70507) = (term571 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438867) (@lem5438767 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438869 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term513 _70504 _70506 _70508 _70505 _70507) = (term572 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438868 _70504 _70506 _70505 _70507 _70508) (@lem5438866 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438870 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5438871 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term521 _70504 _70506 _70508 _70505 _70507) = (term573 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438870) (@lem5438668 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438872 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term522 _70504 _70506 _70508 _70505 _70507) = (term574 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5438871 _70504 _70506 _70505 _70507 _70508) (@lem5438869 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5438874 (_70505 : int) (_70507 : int) (_70508 : int) (_70504 : int) (_70506 : int) : (term575 _70505 _70507 _70508 _70504 _70506) = (term576 _70505 _70507 _70508 _70504 _70506).
Proof. exact (eq_refl (term575 _70505 _70507 _70508 _70504 _70506)). Qed.
Lemma lem5438875 (_70505 : int) (_70507 : int) (_70508 : int) (_70504 : int) (_70506 : int) : (term576 _70505 _70507 _70508 _70504 _70506) = (term575 _70505 _70507 _70508 _70504 _70506).
Proof. exact (SYM (@lem5438874 _70505 _70507 _70508 _70504 _70506)). Qed.
Lemma lem5438876 (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (_70504 : int) : (term575 _70505 _70507 _70508 _70504 _70506) = (term577 _70505 _70506 _70507 _70508 _70504).
Proof. exact (@lem1483205 (real_of_int _70506) (term578 _70504 _70505 _70506 _70507 _70508) (real_of_int _70504)). Qed.
Lemma lem5438877 (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (_70504 : int) : (term576 _70505 _70507 _70508 _70504 _70506) = (term577 _70505 _70506 _70507 _70508 _70504).
Proof. exact (TRANS (@lem5438875 _70505 _70507 _70508 _70504 _70506) (@lem5438876 _70505 _70506 _70507 _70508 _70504)). Qed.
Lemma lem5438878 (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (_70504 : int) : (term579 _70505 _70506 _70507 _70508 _70504) = (term580 _70505 _70506 _70507 _70508 _70504).
Proof. exact (eq_refl (term579 _70505 _70506 _70507 _70508 _70504)). Qed.
Lemma lem5438879 (_70504 : int) (_70506 : int) : (term581 _70504 _70506) = (term581 _70504 _70506).
Proof. exact (eq_refl (term581 _70504 _70506)). Qed.
Lemma lem5438880 (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (_70504 : int) : (term582 _70505 _70506 _70507 _70508 _70504) = (term583 _70505 _70506 _70507 _70508 _70504).
Proof. exact (MK_COMB (@lem5438879 _70504 _70506) (@lem5438878 _70505 _70506 _70507 _70508 _70504)). Qed.
Lemma lem5438881 (_70504 : int) (_70505 : int) (_70507 : int) (_70508 : int) (_70506 : int) : (term584 _70504 _70505 _70507 _70508 _70506) = (term585 _70504 _70505 _70507 _70508 _70506).
Proof. exact (eq_refl (term584 _70504 _70505 _70507 _70508 _70506)). Qed.
Lemma lem5438882 (_70506 : int) (_70504 : int) : (term586 _70506 _70504) = (term586 _70506 _70504).
Proof. exact (eq_refl (term586 _70506 _70504)). Qed.
Lemma lem5438883 (_70504 : int) (_70505 : int) (_70507 : int) (_70508 : int) (_70506 : int) : (term587 _70504 _70505 _70507 _70508 _70506) = (term588 _70504 _70505 _70507 _70508 _70506).
Proof. exact (MK_COMB (@lem5438882 _70506 _70504) (@lem5438881 _70504 _70505 _70507 _70508 _70506)). Qed.
Lemma lem5438884 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5438885 (_70504 : int) (_70505 : int) (_70507 : int) (_70508 : int) (_70506 : int) : (term589 _70504 _70505 _70507 _70508 _70506) = (term590 _70504 _70505 _70507 _70508 _70506).
Proof. exact (MK_COMB (@lem5438884) (@lem5438883 _70504 _70505 _70507 _70508 _70506)). Qed.
Lemma lem5438886 (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (_70504 : int) : (term577 _70505 _70506 _70507 _70508 _70504) = (term591 _70505 _70506 _70507 _70508 _70504).
Proof. exact (MK_COMB (@lem5438885 _70504 _70505 _70507 _70508 _70506) (@lem5438880 _70505 _70506 _70507 _70508 _70504)). Qed.
Lemma lem5438887 (_70505 : int) (_70507 : int) (_70508 : int) (_70504 : int) (_70506 : int) : (term592 _70505 _70507 _70508 _70504 _70506) = (term592 _70505 _70507 _70508 _70504 _70506).
Proof. exact (eq_refl (term592 _70505 _70507 _70508 _70504 _70506)). Qed.
Lemma lem5438888 (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (_70504 : int) : ((term576 _70505 _70507 _70508 _70504 _70506) = (term577 _70505 _70506 _70507 _70508 _70504)) = ((term576 _70505 _70507 _70508 _70504 _70506) = (term591 _70505 _70506 _70507 _70508 _70504)).
Proof. exact (MK_COMB (@lem5438887 _70505 _70507 _70508 _70504 _70506) (@lem5438886 _70505 _70506 _70507 _70508 _70504)). Qed.
Lemma lem5438889 (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (_70504 : int) : (term576 _70505 _70507 _70508 _70504 _70506) = (term591 _70505 _70506 _70507 _70508 _70504).
Proof. exact (EQ_MP (@lem5438888 _70505 _70506 _70507 _70508 _70504) (@lem5438877 _70505 _70506 _70507 _70508 _70504)). Qed.
Lemma lem5438890 (_70506 : int) (_70504 : int) : (term593 _70506 _70504) = (term360 _70506 _70504).
Proof. exact (@lem1988291 (real_of_int _70506) (real_of_int _70504)). Qed.
Lemma lem5438896 (_70506 : int) (_70504 : int) : (term361 _70506 _70504) = (term362 _70506 _70504).
Proof. exact (@lem1982792 (real_of_int _70506) (real_of_int _70504)). Qed.
Lemma lem5438901 (_70504 : int) (_70506 : int) : (term362 _70506 _70504) = (term363 _70504 _70506).
Proof. exact (@lem1982761 (term336 _70504) (real_of_int _70506)). Qed.
Lemma lem5438903 (_70504 : int) (_70506 : int) : (term361 _70506 _70504) = (term363 _70504 _70506).
Proof. exact (TRANS (@lem5438896 _70506 _70504) (@lem5438901 _70504 _70506)). Qed.
Lemma lem5438904 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5438905 (_70504 : int) (_70506 : int) : (term364 _70506 _70504) = (term365 _70504 _70506).
Proof. exact (MK_COMB (@lem5438904) (@lem5438903 _70504 _70506)). Qed.
Lemma lem5438906 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5438907 (_70504 : int) (_70506 : int) : (term360 _70506 _70504) = (term366 _70504 _70506).
Proof. exact (MK_COMB (@lem5438905 _70504 _70506) (@lem5438906)). Qed.
Lemma lem5438908 (_70504 : int) (_70506 : int) : (term593 _70506 _70504) = (term366 _70504 _70506).
Proof. exact (TRANS (@lem5438890 _70506 _70504) (@lem5438907 _70504 _70506)). Qed.
Lemma lem5438909 (_70504 : int) : (term314 _70504) = (term287 _70504).
Proof. exact (@lem1988291 (real_of_int _70504) term214). Qed.
Lemma lem5438915 (_70504 : int) : (term288 _70504) = (term289 _70504).
Proof. exact (@lem1982792 (real_of_int _70504) term214). Qed.
Lemma lem5438917 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5438918 : term214 = term291.
Proof. exact (@lem5438917 (NUMERAL 0)). Qed.
Lemma lem5438920 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5438921 : term294 = term295.
Proof. exact (@lem5438920 term228). Qed.
Lemma lem5438922 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5438923 : term296 = term297.
Proof. exact (MK_COMB (@lem5438922) (@lem5438921)). Qed.
Lemma lem5438924 : term298 = term299.
Proof. exact (MK_COMB (@lem5438923) (@lem5438918)). Qed.
Lemma lem5438925 : term299 = term300.
Proof. exact (@lem1981613 term294 term214 term227 term227). Qed.
Lemma lem5438927 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5438928 : term303 = term304.
Proof. exact (@lem5438927 term228 term228). Qed.
Lemma lem5438929 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5438930 : term306 = term228.
Proof. exact (EQ_MP (@lem5438929) (@lem940073)). Qed.
Lemma lem5438931 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5438932 : term304 = term227.
Proof. exact (MK_COMB (@lem5438931) (@lem5438930)). Qed.
Lemma lem5438933 : term303 = term227.
Proof. exact (TRANS (@lem5438928) (@lem5438932)). Qed.
Lemma lem5438935 (x : nat) : (term307 x) = term214.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5438936 : term298 = term214.
Proof. exact (@lem5438935 term228). Qed.
Lemma lem5438937 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5438938 : term308 = term309.
Proof. exact (MK_COMB (@lem5438937) (@lem5438936)). Qed.
Lemma lem5438939 : term300 = term291.
Proof. exact (MK_COMB (@lem5438938) (@lem5438933)). Qed.
Lemma lem5438940 : term299 = term291.
Proof. exact (TRANS (@lem5438925) (@lem5438939)). Qed.
Lemma lem5438941 : term298 = term291.
Proof. exact (TRANS (@lem5438924) (@lem5438940)). Qed.
Lemma lem5438943 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5438944 : term291 = term214.
Proof. exact (@lem5438943 term214). Qed.
Lemma lem5438945 : term298 = term214.
Proof. exact (TRANS (@lem5438941) (@lem5438944)). Qed.
Lemma lem5438946 (_70504 : int) : (term229 _70504) = (term229 _70504).
Proof. exact (eq_refl (term229 _70504)). Qed.
Lemma lem5438947 (_70504 : int) : (term289 _70504) = (term311 _70504).
Proof. exact (MK_COMB (@lem5438946 _70504) (@lem5438945)). Qed.
Lemma lem5438948 (_70504 : int) : (term311 _70504) = (real_of_int _70504).
Proof. exact (@lem1982723 (real_of_int _70504)). Qed.
Lemma lem5438949 (_70504 : int) : (term289 _70504) = (real_of_int _70504).
Proof. exact (TRANS (@lem5438947 _70504) (@lem5438948 _70504)). Qed.
Lemma lem5438951 (_70504 : int) : (term288 _70504) = (real_of_int _70504).
Proof. exact (TRANS (@lem5438915 _70504) (@lem5438949 _70504)). Qed.
Lemma lem5438952 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5438953 (_70504 : int) : (term312 _70504) = (term313 _70504).
Proof. exact (MK_COMB (@lem5438952) (@lem5438951 _70504)). Qed.
Lemma lem5438954 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5438955 (_70504 : int) : (term287 _70504) = (term314 _70504).
Proof. exact (MK_COMB (@lem5438953 _70504) (@lem5438954)). Qed.
Lemma lem5438956 (_70504 : int) : (term314 _70504) = (term314 _70504).
Proof. exact (TRANS (@lem5438909 _70504) (@lem5438955 _70504)). Qed.
Lemma lem5438957 (_70505 : int) : (term314 _70505) = (term287 _70505).
Proof. exact (@lem1988291 (real_of_int _70505) term214). Qed.
Lemma lem5438963 (_70505 : int) : (term288 _70505) = (term289 _70505).
Proof. exact (@lem1982792 (real_of_int _70505) term214). Qed.
Lemma lem5438965 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5438966 : term214 = term291.
Proof. exact (@lem5438965 (NUMERAL 0)). Qed.
Lemma lem5438968 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5438969 : term294 = term295.
Proof. exact (@lem5438968 term228). Qed.
Lemma lem5438970 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5438971 : term296 = term297.
Proof. exact (MK_COMB (@lem5438970) (@lem5438969)). Qed.
Lemma lem5438972 : term298 = term299.
Proof. exact (MK_COMB (@lem5438971) (@lem5438966)). Qed.
Lemma lem5438973 : term299 = term300.
Proof. exact (@lem1981613 term294 term214 term227 term227). Qed.
Lemma lem5438975 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5438976 : term303 = term304.
Proof. exact (@lem5438975 term228 term228). Qed.
Lemma lem5438977 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5438978 : term306 = term228.
Proof. exact (EQ_MP (@lem5438977) (@lem940073)). Qed.
Lemma lem5438979 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5438980 : term304 = term227.
Proof. exact (MK_COMB (@lem5438979) (@lem5438978)). Qed.
Lemma lem5438981 : term303 = term227.
Proof. exact (TRANS (@lem5438976) (@lem5438980)). Qed.
Lemma lem5438983 (x : nat) : (term307 x) = term214.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5438984 : term298 = term214.
Proof. exact (@lem5438983 term228). Qed.
Lemma lem5438985 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5438986 : term308 = term309.
Proof. exact (MK_COMB (@lem5438985) (@lem5438984)). Qed.
Lemma lem5438987 : term300 = term291.
Proof. exact (MK_COMB (@lem5438986) (@lem5438981)). Qed.
Lemma lem5438988 : term299 = term291.
Proof. exact (TRANS (@lem5438973) (@lem5438987)). Qed.
Lemma lem5438989 : term298 = term291.
Proof. exact (TRANS (@lem5438972) (@lem5438988)). Qed.
Lemma lem5438991 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5438992 : term291 = term214.
Proof. exact (@lem5438991 term214). Qed.
Lemma lem5438993 : term298 = term214.
Proof. exact (TRANS (@lem5438989) (@lem5438992)). Qed.
Lemma lem5438994 (_70505 : int) : (term229 _70505) = (term229 _70505).
Proof. exact (eq_refl (term229 _70505)). Qed.
Lemma lem5438995 (_70505 : int) : (term289 _70505) = (term311 _70505).
Proof. exact (MK_COMB (@lem5438994 _70505) (@lem5438993)). Qed.
Lemma lem5438996 (_70505 : int) : (term311 _70505) = (real_of_int _70505).
Proof. exact (@lem1982723 (real_of_int _70505)). Qed.
Lemma lem5438997 (_70505 : int) : (term289 _70505) = (real_of_int _70505).
Proof. exact (TRANS (@lem5438995 _70505) (@lem5438996 _70505)). Qed.
Lemma lem5438999 (_70505 : int) : (term288 _70505) = (real_of_int _70505).
Proof. exact (TRANS (@lem5438963 _70505) (@lem5438997 _70505)). Qed.
Lemma lem5439000 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5439001 (_70505 : int) : (term312 _70505) = (term313 _70505).
Proof. exact (MK_COMB (@lem5439000) (@lem5438999 _70505)). Qed.
Lemma lem5439002 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5439003 (_70505 : int) : (term287 _70505) = (term314 _70505).
Proof. exact (MK_COMB (@lem5439001 _70505) (@lem5439002)). Qed.
Lemma lem5439004 (_70505 : int) : (term314 _70505) = (term314 _70505).
Proof. exact (TRANS (@lem5438957 _70505) (@lem5439003 _70505)). Qed.
Lemma lem5439005 (_70506 : int) : (term314 _70506) = (term287 _70506).
Proof. exact (@lem1988291 (real_of_int _70506) term214). Qed.
Lemma lem5439011 (_70506 : int) : (term288 _70506) = (term289 _70506).
Proof. exact (@lem1982792 (real_of_int _70506) term214). Qed.
Lemma lem5439013 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5439014 : term214 = term291.
Proof. exact (@lem5439013 (NUMERAL 0)). Qed.
Lemma lem5439016 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5439017 : term294 = term295.
Proof. exact (@lem5439016 term228). Qed.
Lemma lem5439018 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5439019 : term296 = term297.
Proof. exact (MK_COMB (@lem5439018) (@lem5439017)). Qed.
Lemma lem5439020 : term298 = term299.
Proof. exact (MK_COMB (@lem5439019) (@lem5439014)). Qed.
Lemma lem5439021 : term299 = term300.
Proof. exact (@lem1981613 term294 term214 term227 term227). Qed.
Lemma lem5439023 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5439024 : term303 = term304.
Proof. exact (@lem5439023 term228 term228). Qed.
Lemma lem5439025 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5439026 : term306 = term228.
Proof. exact (EQ_MP (@lem5439025) (@lem940073)). Qed.
Lemma lem5439027 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5439028 : term304 = term227.
Proof. exact (MK_COMB (@lem5439027) (@lem5439026)). Qed.
Lemma lem5439029 : term303 = term227.
Proof. exact (TRANS (@lem5439024) (@lem5439028)). Qed.
Lemma lem5439031 (x : nat) : (term307 x) = term214.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5439032 : term298 = term214.
Proof. exact (@lem5439031 term228). Qed.
Lemma lem5439033 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5439034 : term308 = term309.
Proof. exact (MK_COMB (@lem5439033) (@lem5439032)). Qed.
Lemma lem5439035 : term300 = term291.
Proof. exact (MK_COMB (@lem5439034) (@lem5439029)). Qed.
Lemma lem5439036 : term299 = term291.
Proof. exact (TRANS (@lem5439021) (@lem5439035)). Qed.
Lemma lem5439037 : term298 = term291.
Proof. exact (TRANS (@lem5439020) (@lem5439036)). Qed.
Lemma lem5439039 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5439040 : term291 = term214.
Proof. exact (@lem5439039 term214). Qed.
Lemma lem5439041 : term298 = term214.
Proof. exact (TRANS (@lem5439037) (@lem5439040)). Qed.
Lemma lem5439042 (_70506 : int) : (term229 _70506) = (term229 _70506).
Proof. exact (eq_refl (term229 _70506)). Qed.
Lemma lem5439043 (_70506 : int) : (term289 _70506) = (term311 _70506).
Proof. exact (MK_COMB (@lem5439042 _70506) (@lem5439041)). Qed.
Lemma lem5439044 (_70506 : int) : (term311 _70506) = (real_of_int _70506).
Proof. exact (@lem1982723 (real_of_int _70506)). Qed.
Lemma lem5439045 (_70506 : int) : (term289 _70506) = (real_of_int _70506).
Proof. exact (TRANS (@lem5439043 _70506) (@lem5439044 _70506)). Qed.
Lemma lem5439047 (_70506 : int) : (term288 _70506) = (real_of_int _70506).
Proof. exact (TRANS (@lem5439011 _70506) (@lem5439045 _70506)). Qed.
Lemma lem5439048 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5439049 (_70506 : int) : (term312 _70506) = (term313 _70506).
Proof. exact (MK_COMB (@lem5439048) (@lem5439047 _70506)). Qed.
Lemma lem5439050 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5439051 (_70506 : int) : (term287 _70506) = (term314 _70506).
Proof. exact (MK_COMB (@lem5439049 _70506) (@lem5439050)). Qed.
Lemma lem5439052 (_70506 : int) : (term314 _70506) = (term314 _70506).
Proof. exact (TRANS (@lem5439005 _70506) (@lem5439051 _70506)). Qed.
Lemma lem5439053 (_70507 : int) : (term314 _70507) = (term287 _70507).
Proof. exact (@lem1988291 (real_of_int _70507) term214). Qed.
Lemma lem5439059 (_70507 : int) : (term288 _70507) = (term289 _70507).
Proof. exact (@lem1982792 (real_of_int _70507) term214). Qed.
Lemma lem5439061 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5439062 : term214 = term291.
Proof. exact (@lem5439061 (NUMERAL 0)). Qed.
Lemma lem5439064 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5439065 : term294 = term295.
Proof. exact (@lem5439064 term228). Qed.
Lemma lem5439066 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5439067 : term296 = term297.
Proof. exact (MK_COMB (@lem5439066) (@lem5439065)). Qed.
Lemma lem5439068 : term298 = term299.
Proof. exact (MK_COMB (@lem5439067) (@lem5439062)). Qed.
Lemma lem5439069 : term299 = term300.
Proof. exact (@lem1981613 term294 term214 term227 term227). Qed.
Lemma lem5439071 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5439072 : term303 = term304.
Proof. exact (@lem5439071 term228 term228). Qed.
Lemma lem5439073 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5439074 : term306 = term228.
Proof. exact (EQ_MP (@lem5439073) (@lem940073)). Qed.
Lemma lem5439075 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5439076 : term304 = term227.
Proof. exact (MK_COMB (@lem5439075) (@lem5439074)). Qed.
Lemma lem5439077 : term303 = term227.
Proof. exact (TRANS (@lem5439072) (@lem5439076)). Qed.
Lemma lem5439079 (x : nat) : (term307 x) = term214.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5439080 : term298 = term214.
Proof. exact (@lem5439079 term228). Qed.
Lemma lem5439081 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5439082 : term308 = term309.
Proof. exact (MK_COMB (@lem5439081) (@lem5439080)). Qed.
Lemma lem5439083 : term300 = term291.
Proof. exact (MK_COMB (@lem5439082) (@lem5439077)). Qed.
Lemma lem5439084 : term299 = term291.
Proof. exact (TRANS (@lem5439069) (@lem5439083)). Qed.
Lemma lem5439085 : term298 = term291.
Proof. exact (TRANS (@lem5439068) (@lem5439084)). Qed.
Lemma lem5439087 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5439088 : term291 = term214.
Proof. exact (@lem5439087 term214). Qed.
Lemma lem5439089 : term298 = term214.
Proof. exact (TRANS (@lem5439085) (@lem5439088)). Qed.
Lemma lem5439090 (_70507 : int) : (term229 _70507) = (term229 _70507).
Proof. exact (eq_refl (term229 _70507)). Qed.
Lemma lem5439091 (_70507 : int) : (term289 _70507) = (term311 _70507).
Proof. exact (MK_COMB (@lem5439090 _70507) (@lem5439089)). Qed.
Lemma lem5439092 (_70507 : int) : (term311 _70507) = (real_of_int _70507).
Proof. exact (@lem1982723 (real_of_int _70507)). Qed.
Lemma lem5439093 (_70507 : int) : (term289 _70507) = (real_of_int _70507).
Proof. exact (TRANS (@lem5439091 _70507) (@lem5439092 _70507)). Qed.
Lemma lem5439095 (_70507 : int) : (term288 _70507) = (real_of_int _70507).
Proof. exact (TRANS (@lem5439059 _70507) (@lem5439093 _70507)). Qed.
Lemma lem5439096 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5439097 (_70507 : int) : (term312 _70507) = (term313 _70507).
Proof. exact (MK_COMB (@lem5439096) (@lem5439095 _70507)). Qed.
Lemma lem5439098 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5439099 (_70507 : int) : (term287 _70507) = (term314 _70507).
Proof. exact (MK_COMB (@lem5439097 _70507) (@lem5439098)). Qed.
Lemma lem5439100 (_70507 : int) : (term314 _70507) = (term314 _70507).
Proof. exact (TRANS (@lem5439053 _70507) (@lem5439099 _70507)). Qed.
Lemma lem5439101 (_70508 : int) : (term314 _70508) = (term287 _70508).
Proof. exact (@lem1988291 (real_of_int _70508) term214). Qed.
Lemma lem5439107 (_70508 : int) : (term288 _70508) = (term289 _70508).
Proof. exact (@lem1982792 (real_of_int _70508) term214). Qed.
Lemma lem5439109 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5439110 : term214 = term291.
Proof. exact (@lem5439109 (NUMERAL 0)). Qed.
Lemma lem5439112 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5439113 : term294 = term295.
Proof. exact (@lem5439112 term228). Qed.
Lemma lem5439114 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5439115 : term296 = term297.
Proof. exact (MK_COMB (@lem5439114) (@lem5439113)). Qed.
Lemma lem5439116 : term298 = term299.
Proof. exact (MK_COMB (@lem5439115) (@lem5439110)). Qed.
Lemma lem5439117 : term299 = term300.
Proof. exact (@lem1981613 term294 term214 term227 term227). Qed.
Lemma lem5439119 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5439120 : term303 = term304.
Proof. exact (@lem5439119 term228 term228). Qed.
Lemma lem5439121 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5439122 : term306 = term228.
Proof. exact (EQ_MP (@lem5439121) (@lem940073)). Qed.
Lemma lem5439123 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5439124 : term304 = term227.
Proof. exact (MK_COMB (@lem5439123) (@lem5439122)). Qed.
Lemma lem5439125 : term303 = term227.
Proof. exact (TRANS (@lem5439120) (@lem5439124)). Qed.
Lemma lem5439127 (x : nat) : (term307 x) = term214.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5439128 : term298 = term214.
Proof. exact (@lem5439127 term228). Qed.
Lemma lem5439129 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5439130 : term308 = term309.
Proof. exact (MK_COMB (@lem5439129) (@lem5439128)). Qed.
Lemma lem5439131 : term300 = term291.
Proof. exact (MK_COMB (@lem5439130) (@lem5439125)). Qed.
Lemma lem5439132 : term299 = term291.
Proof. exact (TRANS (@lem5439117) (@lem5439131)). Qed.
Lemma lem5439133 : term298 = term291.
Proof. exact (TRANS (@lem5439116) (@lem5439132)). Qed.
Lemma lem5439135 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5439136 : term291 = term214.
Proof. exact (@lem5439135 term214). Qed.
Lemma lem5439137 : term298 = term214.
Proof. exact (TRANS (@lem5439133) (@lem5439136)). Qed.
Lemma lem5439138 (_70508 : int) : (term229 _70508) = (term229 _70508).
Proof. exact (eq_refl (term229 _70508)). Qed.
Lemma lem5439139 (_70508 : int) : (term289 _70508) = (term311 _70508).
Proof. exact (MK_COMB (@lem5439138 _70508) (@lem5439137)). Qed.
Lemma lem5439140 (_70508 : int) : (term311 _70508) = (real_of_int _70508).
Proof. exact (@lem1982723 (real_of_int _70508)). Qed.
Lemma lem5439141 (_70508 : int) : (term289 _70508) = (real_of_int _70508).
Proof. exact (TRANS (@lem5439139 _70508) (@lem5439140 _70508)). Qed.
Lemma lem5439143 (_70508 : int) : (term288 _70508) = (real_of_int _70508).
Proof. exact (TRANS (@lem5439107 _70508) (@lem5439141 _70508)). Qed.
Lemma lem5439144 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5439145 (_70508 : int) : (term312 _70508) = (term313 _70508).
Proof. exact (MK_COMB (@lem5439144) (@lem5439143 _70508)). Qed.
Lemma lem5439146 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5439147 (_70508 : int) : (term287 _70508) = (term314 _70508).
Proof. exact (MK_COMB (@lem5439145 _70508) (@lem5439146)). Qed.
Lemma lem5439148 (_70508 : int) : (term314 _70508) = (term314 _70508).
Proof. exact (TRANS (@lem5439101 _70508) (@lem5439147 _70508)). Qed.
Lemma lem5439149 (_70504 : int) (_70508 : int) : (term366 _70504 _70508) = (term594 _70504 _70508).
Proof. exact (@lem1988291 (term363 _70504 _70508) term214). Qed.
Lemma lem5439167 (_70504 : int) (_70508 : int) : (term595 _70504 _70508) = (term596 _70504 _70508).
Proof. exact (@lem1982792 (term363 _70504 _70508) term214). Qed.
Lemma lem5439169 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5439170 : term214 = term291.
Proof. exact (@lem5439169 (NUMERAL 0)). Qed.
Lemma lem5439172 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5439173 : term294 = term295.
Proof. exact (@lem5439172 term228). Qed.
Lemma lem5439174 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5439175 : term296 = term297.
Proof. exact (MK_COMB (@lem5439174) (@lem5439173)). Qed.
Lemma lem5439176 : term298 = term299.
Proof. exact (MK_COMB (@lem5439175) (@lem5439170)). Qed.
Lemma lem5439177 : term299 = term300.
Proof. exact (@lem1981613 term294 term214 term227 term227). Qed.
Lemma lem5439179 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5439180 : term303 = term304.
Proof. exact (@lem5439179 term228 term228). Qed.
Lemma lem5439181 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5439182 : term306 = term228.
Proof. exact (EQ_MP (@lem5439181) (@lem940073)). Qed.
Lemma lem5439183 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5439184 : term304 = term227.
Proof. exact (MK_COMB (@lem5439183) (@lem5439182)). Qed.
Lemma lem5439185 : term303 = term227.
Proof. exact (TRANS (@lem5439180) (@lem5439184)). Qed.
Lemma lem5439187 (x : nat) : (term307 x) = term214.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5439188 : term298 = term214.
Proof. exact (@lem5439187 term228). Qed.
Lemma lem5439189 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5439190 : term308 = term309.
Proof. exact (MK_COMB (@lem5439189) (@lem5439188)). Qed.
Lemma lem5439191 : term300 = term291.
Proof. exact (MK_COMB (@lem5439190) (@lem5439185)). Qed.
Lemma lem5439192 : term299 = term291.
Proof. exact (TRANS (@lem5439177) (@lem5439191)). Qed.
Lemma lem5439193 : term298 = term291.
Proof. exact (TRANS (@lem5439176) (@lem5439192)). Qed.
Lemma lem5439195 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5439196 : term291 = term214.
Proof. exact (@lem5439195 term214). Qed.
Lemma lem5439197 : term298 = term214.
Proof. exact (TRANS (@lem5439193) (@lem5439196)). Qed.
Lemma lem5439198 (_70504 : int) (_70508 : int) : (term597 _70504 _70508) = (term597 _70504 _70508).
Proof. exact (eq_refl (term597 _70504 _70508)). Qed.
Lemma lem5439199 (_70504 : int) (_70508 : int) : (term596 _70504 _70508) = (term598 _70504 _70508).
Proof. exact (MK_COMB (@lem5439198 _70504 _70508) (@lem5439197)). Qed.
Lemma lem5439200 (_70504 : int) (_70508 : int) : (term598 _70504 _70508) = (term363 _70504 _70508).
Proof. exact (@lem1982723 (term363 _70504 _70508)). Qed.
Lemma lem5439201 (_70504 : int) (_70508 : int) : (term596 _70504 _70508) = (term363 _70504 _70508).
Proof. exact (TRANS (@lem5439199 _70504 _70508) (@lem5439200 _70504 _70508)). Qed.
Lemma lem5439203 (_70504 : int) (_70508 : int) : (term595 _70504 _70508) = (term363 _70504 _70508).
Proof. exact (TRANS (@lem5439167 _70504 _70508) (@lem5439201 _70504 _70508)). Qed.
Lemma lem5439204 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5439205 (_70504 : int) (_70508 : int) : (term599 _70504 _70508) = (term365 _70504 _70508).
Proof. exact (MK_COMB (@lem5439204) (@lem5439203 _70504 _70508)). Qed.
Lemma lem5439206 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5439207 (_70504 : int) (_70508 : int) : (term594 _70504 _70508) = (term366 _70504 _70508).
Proof. exact (MK_COMB (@lem5439205 _70504 _70508) (@lem5439206)). Qed.
Lemma lem5439208 (_70504 : int) (_70508 : int) : (term366 _70504 _70508) = (term366 _70504 _70508).
Proof. exact (TRANS (@lem5439149 _70504 _70508) (@lem5439207 _70504 _70508)). Qed.
Lemma lem5439209 (_70505 : int) (_70508 : int) : (term368 _70505 _70508) = (term600 _70505 _70508).
Proof. exact (@lem1988291 (term362 _70505 _70508) term214). Qed.
Lemma lem5439227 (_70505 : int) (_70508 : int) : (term601 _70505 _70508) = (term602 _70505 _70508).
Proof. exact (@lem1982792 (term362 _70505 _70508) term214). Qed.
Lemma lem5439229 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5439230 : term214 = term291.
Proof. exact (@lem5439229 (NUMERAL 0)). Qed.
Lemma lem5439232 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5439233 : term294 = term295.
Proof. exact (@lem5439232 term228). Qed.
Lemma lem5439234 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5439235 : term296 = term297.
Proof. exact (MK_COMB (@lem5439234) (@lem5439233)). Qed.
Lemma lem5439236 : term298 = term299.
Proof. exact (MK_COMB (@lem5439235) (@lem5439230)). Qed.
Lemma lem5439237 : term299 = term300.
Proof. exact (@lem1981613 term294 term214 term227 term227). Qed.
Lemma lem5439239 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5439240 : term303 = term304.
Proof. exact (@lem5439239 term228 term228). Qed.
Lemma lem5439241 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5439242 : term306 = term228.
Proof. exact (EQ_MP (@lem5439241) (@lem940073)). Qed.
Lemma lem5439243 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5439244 : term304 = term227.
Proof. exact (MK_COMB (@lem5439243) (@lem5439242)). Qed.
Lemma lem5439245 : term303 = term227.
Proof. exact (TRANS (@lem5439240) (@lem5439244)). Qed.
Lemma lem5439247 (x : nat) : (term307 x) = term214.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5439248 : term298 = term214.
Proof. exact (@lem5439247 term228). Qed.
Lemma lem5439249 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5439250 : term308 = term309.
Proof. exact (MK_COMB (@lem5439249) (@lem5439248)). Qed.
Lemma lem5439251 : term300 = term291.
Proof. exact (MK_COMB (@lem5439250) (@lem5439245)). Qed.
Lemma lem5439252 : term299 = term291.
Proof. exact (TRANS (@lem5439237) (@lem5439251)). Qed.
Lemma lem5439253 : term298 = term291.
Proof. exact (TRANS (@lem5439236) (@lem5439252)). Qed.
Lemma lem5439255 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5439256 : term291 = term214.
Proof. exact (@lem5439255 term214). Qed.
Lemma lem5439257 : term298 = term214.
Proof. exact (TRANS (@lem5439253) (@lem5439256)). Qed.
Lemma lem5439258 (_70505 : int) (_70508 : int) : (term603 _70505 _70508) = (term603 _70505 _70508).
Proof. exact (eq_refl (term603 _70505 _70508)). Qed.
Lemma lem5439259 (_70505 : int) (_70508 : int) : (term602 _70505 _70508) = (term604 _70505 _70508).
Proof. exact (MK_COMB (@lem5439258 _70505 _70508) (@lem5439257)). Qed.
Lemma lem5439260 (_70505 : int) (_70508 : int) : (term604 _70505 _70508) = (term362 _70505 _70508).
Proof. exact (@lem1982723 (term362 _70505 _70508)). Qed.
Lemma lem5439261 (_70505 : int) (_70508 : int) : (term602 _70505 _70508) = (term362 _70505 _70508).
Proof. exact (TRANS (@lem5439259 _70505 _70508) (@lem5439260 _70505 _70508)). Qed.
Lemma lem5439263 (_70505 : int) (_70508 : int) : (term601 _70505 _70508) = (term362 _70505 _70508).
Proof. exact (TRANS (@lem5439227 _70505 _70508) (@lem5439261 _70505 _70508)). Qed.
Lemma lem5439264 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5439265 (_70505 : int) (_70508 : int) : (term605 _70505 _70508) = (term367 _70505 _70508).
Proof. exact (MK_COMB (@lem5439264) (@lem5439263 _70505 _70508)). Qed.
Lemma lem5439266 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5439267 (_70505 : int) (_70508 : int) : (term600 _70505 _70508) = (term368 _70505 _70508).
Proof. exact (MK_COMB (@lem5439265 _70505 _70508) (@lem5439266)). Qed.
Lemma lem5439268 (_70505 : int) (_70508 : int) : (term368 _70505 _70508) = (term368 _70505 _70508).
Proof. exact (TRANS (@lem5439209 _70505 _70508) (@lem5439267 _70505 _70508)). Qed.
Lemma lem5439269 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439270 (_70504 : int) (_70508 : int) : (term369 _70504 _70508) = (term369 _70504 _70508).
Proof. exact (MK_COMB (@lem5439269) (@lem5439208 _70504 _70508)). Qed.
Lemma lem5439271 (_70504 : int) (_70505 : int) (_70508 : int) : (term370 _70504 _70505 _70508) = (term370 _70504 _70505 _70508).
Proof. exact (MK_COMB (@lem5439270 _70504 _70508) (@lem5439268 _70505 _70508)). Qed.
Lemma lem5439272 (_70506 : int) (_70508 : int) : (term366 _70506 _70508) = (term594 _70506 _70508).
Proof. exact (@lem1988291 (term363 _70506 _70508) term214). Qed.
Lemma lem5439290 (_70506 : int) (_70508 : int) : (term595 _70506 _70508) = (term596 _70506 _70508).
Proof. exact (@lem1982792 (term363 _70506 _70508) term214). Qed.
Lemma lem5439292 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5439293 : term214 = term291.
Proof. exact (@lem5439292 (NUMERAL 0)). Qed.
Lemma lem5439295 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5439296 : term294 = term295.
Proof. exact (@lem5439295 term228). Qed.
Lemma lem5439297 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5439298 : term296 = term297.
Proof. exact (MK_COMB (@lem5439297) (@lem5439296)). Qed.
Lemma lem5439299 : term298 = term299.
Proof. exact (MK_COMB (@lem5439298) (@lem5439293)). Qed.
Lemma lem5439300 : term299 = term300.
Proof. exact (@lem1981613 term294 term214 term227 term227). Qed.
Lemma lem5439302 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5439303 : term303 = term304.
Proof. exact (@lem5439302 term228 term228). Qed.
Lemma lem5439304 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5439305 : term306 = term228.
Proof. exact (EQ_MP (@lem5439304) (@lem940073)). Qed.
Lemma lem5439306 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5439307 : term304 = term227.
Proof. exact (MK_COMB (@lem5439306) (@lem5439305)). Qed.
Lemma lem5439308 : term303 = term227.
Proof. exact (TRANS (@lem5439303) (@lem5439307)). Qed.
Lemma lem5439310 (x : nat) : (term307 x) = term214.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5439311 : term298 = term214.
Proof. exact (@lem5439310 term228). Qed.
Lemma lem5439312 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5439313 : term308 = term309.
Proof. exact (MK_COMB (@lem5439312) (@lem5439311)). Qed.
Lemma lem5439314 : term300 = term291.
Proof. exact (MK_COMB (@lem5439313) (@lem5439308)). Qed.
Lemma lem5439315 : term299 = term291.
Proof. exact (TRANS (@lem5439300) (@lem5439314)). Qed.
Lemma lem5439316 : term298 = term291.
Proof. exact (TRANS (@lem5439299) (@lem5439315)). Qed.
Lemma lem5439318 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5439319 : term291 = term214.
Proof. exact (@lem5439318 term214). Qed.
Lemma lem5439320 : term298 = term214.
Proof. exact (TRANS (@lem5439316) (@lem5439319)). Qed.
Lemma lem5439321 (_70506 : int) (_70508 : int) : (term597 _70506 _70508) = (term597 _70506 _70508).
Proof. exact (eq_refl (term597 _70506 _70508)). Qed.
Lemma lem5439322 (_70506 : int) (_70508 : int) : (term596 _70506 _70508) = (term598 _70506 _70508).
Proof. exact (MK_COMB (@lem5439321 _70506 _70508) (@lem5439320)). Qed.
Lemma lem5439323 (_70506 : int) (_70508 : int) : (term598 _70506 _70508) = (term363 _70506 _70508).
Proof. exact (@lem1982723 (term363 _70506 _70508)). Qed.
Lemma lem5439324 (_70506 : int) (_70508 : int) : (term596 _70506 _70508) = (term363 _70506 _70508).
Proof. exact (TRANS (@lem5439322 _70506 _70508) (@lem5439323 _70506 _70508)). Qed.
Lemma lem5439326 (_70506 : int) (_70508 : int) : (term595 _70506 _70508) = (term363 _70506 _70508).
Proof. exact (TRANS (@lem5439290 _70506 _70508) (@lem5439324 _70506 _70508)). Qed.
Lemma lem5439327 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5439328 (_70506 : int) (_70508 : int) : (term599 _70506 _70508) = (term365 _70506 _70508).
Proof. exact (MK_COMB (@lem5439327) (@lem5439326 _70506 _70508)). Qed.
Lemma lem5439329 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5439330 (_70506 : int) (_70508 : int) : (term594 _70506 _70508) = (term366 _70506 _70508).
Proof. exact (MK_COMB (@lem5439328 _70506 _70508) (@lem5439329)). Qed.
Lemma lem5439331 (_70506 : int) (_70508 : int) : (term366 _70506 _70508) = (term366 _70506 _70508).
Proof. exact (TRANS (@lem5439272 _70506 _70508) (@lem5439330 _70506 _70508)). Qed.
Lemma lem5439332 (_70507 : int) (_70508 : int) : (term368 _70507 _70508) = (term600 _70507 _70508).
Proof. exact (@lem1988291 (term362 _70507 _70508) term214). Qed.
Lemma lem5439350 (_70507 : int) (_70508 : int) : (term601 _70507 _70508) = (term602 _70507 _70508).
Proof. exact (@lem1982792 (term362 _70507 _70508) term214). Qed.
Lemma lem5439352 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5439353 : term214 = term291.
Proof. exact (@lem5439352 (NUMERAL 0)). Qed.
Lemma lem5439355 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5439356 : term294 = term295.
Proof. exact (@lem5439355 term228). Qed.
Lemma lem5439357 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5439358 : term296 = term297.
Proof. exact (MK_COMB (@lem5439357) (@lem5439356)). Qed.
Lemma lem5439359 : term298 = term299.
Proof. exact (MK_COMB (@lem5439358) (@lem5439353)). Qed.
Lemma lem5439360 : term299 = term300.
Proof. exact (@lem1981613 term294 term214 term227 term227). Qed.
Lemma lem5439362 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5439363 : term303 = term304.
Proof. exact (@lem5439362 term228 term228). Qed.
Lemma lem5439364 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5439365 : term306 = term228.
Proof. exact (EQ_MP (@lem5439364) (@lem940073)). Qed.
Lemma lem5439366 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5439367 : term304 = term227.
Proof. exact (MK_COMB (@lem5439366) (@lem5439365)). Qed.
Lemma lem5439368 : term303 = term227.
Proof. exact (TRANS (@lem5439363) (@lem5439367)). Qed.
Lemma lem5439370 (x : nat) : (term307 x) = term214.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5439371 : term298 = term214.
Proof. exact (@lem5439370 term228). Qed.
Lemma lem5439372 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5439373 : term308 = term309.
Proof. exact (MK_COMB (@lem5439372) (@lem5439371)). Qed.
Lemma lem5439374 : term300 = term291.
Proof. exact (MK_COMB (@lem5439373) (@lem5439368)). Qed.
Lemma lem5439375 : term299 = term291.
Proof. exact (TRANS (@lem5439360) (@lem5439374)). Qed.
Lemma lem5439376 : term298 = term291.
Proof. exact (TRANS (@lem5439359) (@lem5439375)). Qed.
Lemma lem5439378 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5439379 : term291 = term214.
Proof. exact (@lem5439378 term214). Qed.
Lemma lem5439380 : term298 = term214.
Proof. exact (TRANS (@lem5439376) (@lem5439379)). Qed.
Lemma lem5439381 (_70507 : int) (_70508 : int) : (term603 _70507 _70508) = (term603 _70507 _70508).
Proof. exact (eq_refl (term603 _70507 _70508)). Qed.
Lemma lem5439382 (_70507 : int) (_70508 : int) : (term602 _70507 _70508) = (term604 _70507 _70508).
Proof. exact (MK_COMB (@lem5439381 _70507 _70508) (@lem5439380)). Qed.
Lemma lem5439383 (_70507 : int) (_70508 : int) : (term604 _70507 _70508) = (term362 _70507 _70508).
Proof. exact (@lem1982723 (term362 _70507 _70508)). Qed.
Lemma lem5439384 (_70507 : int) (_70508 : int) : (term602 _70507 _70508) = (term362 _70507 _70508).
Proof. exact (TRANS (@lem5439382 _70507 _70508) (@lem5439383 _70507 _70508)). Qed.
Lemma lem5439386 (_70507 : int) (_70508 : int) : (term601 _70507 _70508) = (term362 _70507 _70508).
Proof. exact (TRANS (@lem5439350 _70507 _70508) (@lem5439384 _70507 _70508)). Qed.
Lemma lem5439387 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5439388 (_70507 : int) (_70508 : int) : (term605 _70507 _70508) = (term367 _70507 _70508).
Proof. exact (MK_COMB (@lem5439387) (@lem5439386 _70507 _70508)). Qed.
Lemma lem5439389 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5439390 (_70507 : int) (_70508 : int) : (term600 _70507 _70508) = (term368 _70507 _70508).
Proof. exact (MK_COMB (@lem5439388 _70507 _70508) (@lem5439389)). Qed.
Lemma lem5439391 (_70507 : int) (_70508 : int) : (term368 _70507 _70508) = (term368 _70507 _70508).
Proof. exact (TRANS (@lem5439332 _70507 _70508) (@lem5439390 _70507 _70508)). Qed.
Lemma lem5439392 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439393 (_70506 : int) (_70508 : int) : (term369 _70506 _70508) = (term369 _70506 _70508).
Proof. exact (MK_COMB (@lem5439392) (@lem5439331 _70506 _70508)). Qed.
Lemma lem5439394 (_70506 : int) (_70507 : int) (_70508 : int) : (term370 _70506 _70507 _70508) = (term370 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5439393 _70506 _70508) (@lem5439391 _70507 _70508)). Qed.
Lemma lem5439395 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439396 (_70504 : int) (_70505 : int) (_70508 : int) : (term371 _70504 _70505 _70508) = (term371 _70504 _70505 _70508).
Proof. exact (MK_COMB (@lem5439395) (@lem5439271 _70504 _70505 _70508)). Qed.
Lemma lem5439397 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) : (term372 _70504 _70505 _70506 _70507 _70508) = (term372 _70504 _70505 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5439396 _70504 _70505 _70508) (@lem5439394 _70506 _70507 _70508)). Qed.
Lemma lem5439398 (_70508 : int) (_70506 : int) : (term338 _70508 _70506) = (term606 _70508 _70506).
Proof. exact (@lem1988291 (term335 _70508 _70506) term214). Qed.
Lemma lem5439399 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5439422 (_70506 : int) (_70508 : int) : (term335 _70508 _70506) = (term331 _70506 _70508).
Proof. exact (@lem1982757 (real_of_int _70506) (term336 _70508) term294). Qed.
Lemma lem5439423 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem5439424 (_70506 : int) (_70508 : int) : (term607 _70508 _70506) = (term608 _70506 _70508).
Proof. exact (MK_COMB (@lem5439423) (@lem5439422 _70506 _70508)). Qed.
Lemma lem5439425 (_70506 : int) (_70508 : int) : (term609 _70508 _70506) = (term610 _70506 _70508).
Proof. exact (MK_COMB (@lem5439424 _70506 _70508) (@lem5439399)). Qed.
Lemma lem5439426 (_70506 : int) (_70508 : int) : (term610 _70506 _70508) = (term611 _70506 _70508).
Proof. exact (@lem1982792 (term331 _70506 _70508) term214). Qed.
Lemma lem5439428 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5439429 : term214 = term291.
Proof. exact (@lem5439428 (NUMERAL 0)). Qed.
Lemma lem5439431 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5439432 : term294 = term295.
Proof. exact (@lem5439431 term228). Qed.
Lemma lem5439433 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5439434 : term296 = term297.
Proof. exact (MK_COMB (@lem5439433) (@lem5439432)). Qed.
Lemma lem5439435 : term298 = term299.
Proof. exact (MK_COMB (@lem5439434) (@lem5439429)). Qed.
Lemma lem5439436 : term299 = term300.
Proof. exact (@lem1981613 term294 term214 term227 term227). Qed.
Lemma lem5439438 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5439439 : term303 = term304.
Proof. exact (@lem5439438 term228 term228). Qed.
Lemma lem5439440 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5439441 : term306 = term228.
Proof. exact (EQ_MP (@lem5439440) (@lem940073)). Qed.
Lemma lem5439442 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5439443 : term304 = term227.
Proof. exact (MK_COMB (@lem5439442) (@lem5439441)). Qed.
Lemma lem5439444 : term303 = term227.
Proof. exact (TRANS (@lem5439439) (@lem5439443)). Qed.
Lemma lem5439446 (x : nat) : (term307 x) = term214.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5439447 : term298 = term214.
Proof. exact (@lem5439446 term228). Qed.
Lemma lem5439448 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5439449 : term308 = term309.
Proof. exact (MK_COMB (@lem5439448) (@lem5439447)). Qed.
Lemma lem5439450 : term300 = term291.
Proof. exact (MK_COMB (@lem5439449) (@lem5439444)). Qed.
Lemma lem5439451 : term299 = term291.
Proof. exact (TRANS (@lem5439436) (@lem5439450)). Qed.
Lemma lem5439452 : term298 = term291.
Proof. exact (TRANS (@lem5439435) (@lem5439451)). Qed.
Lemma lem5439454 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5439455 : term291 = term214.
Proof. exact (@lem5439454 term214). Qed.
Lemma lem5439456 : term298 = term214.
Proof. exact (TRANS (@lem5439452) (@lem5439455)). Qed.
Lemma lem5439457 (_70506 : int) (_70508 : int) : (term612 _70506 _70508) = (term612 _70506 _70508).
Proof. exact (eq_refl (term612 _70506 _70508)). Qed.
Lemma lem5439458 (_70506 : int) (_70508 : int) : (term611 _70506 _70508) = (term613 _70506 _70508).
Proof. exact (MK_COMB (@lem5439457 _70506 _70508) (@lem5439456)). Qed.
Lemma lem5439459 (_70506 : int) (_70508 : int) : (term613 _70506 _70508) = (term331 _70506 _70508).
Proof. exact (@lem1982723 (term331 _70506 _70508)). Qed.
Lemma lem5439460 (_70506 : int) (_70508 : int) : (term611 _70506 _70508) = (term331 _70506 _70508).
Proof. exact (TRANS (@lem5439458 _70506 _70508) (@lem5439459 _70506 _70508)). Qed.
Lemma lem5439461 (_70506 : int) (_70508 : int) : (term610 _70506 _70508) = (term331 _70506 _70508).
Proof. exact (TRANS (@lem5439426 _70506 _70508) (@lem5439460 _70506 _70508)). Qed.
Lemma lem5439462 (_70506 : int) (_70508 : int) : (term609 _70508 _70506) = (term331 _70506 _70508).
Proof. exact (TRANS (@lem5439425 _70506 _70508) (@lem5439461 _70506 _70508)). Qed.
Lemma lem5439463 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5439464 (_70506 : int) (_70508 : int) : (term614 _70508 _70506) = (term333 _70506 _70508).
Proof. exact (MK_COMB (@lem5439463) (@lem5439462 _70506 _70508)). Qed.
Lemma lem5439465 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5439466 (_70506 : int) (_70508 : int) : (term606 _70508 _70506) = (term334 _70506 _70508).
Proof. exact (MK_COMB (@lem5439464 _70506 _70508) (@lem5439465)). Qed.
Lemma lem5439467 (_70506 : int) (_70508 : int) : (term338 _70508 _70506) = (term334 _70506 _70508).
Proof. exact (TRANS (@lem5439398 _70508 _70506) (@lem5439466 _70506 _70508)). Qed.
Lemma lem5439468 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439469 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) : (term395 _70504 _70505 _70506 _70507 _70508) = (term395 _70504 _70505 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5439468) (@lem5439397 _70504 _70505 _70506 _70507 _70508)). Qed.
Lemma lem5439470 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) : (term615 _70504 _70505 _70507 _70508 _70506) = (term616 _70504 _70505 _70507 _70506 _70508).
Proof. exact (MK_COMB (@lem5439469 _70504 _70505 _70506 _70507 _70508) (@lem5439467 _70506 _70508)). Qed.
Lemma lem5439471 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439472 (_70508 : int) : (term399 _70508) = (term399 _70508).
Proof. exact (MK_COMB (@lem5439471) (@lem5439148 _70508)). Qed.
Lemma lem5439473 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) : (term617 _70504 _70505 _70507 _70508 _70506) = (term618 _70504 _70505 _70507 _70506 _70508).
Proof. exact (MK_COMB (@lem5439472 _70508) (@lem5439470 _70504 _70505 _70507 _70506 _70508)). Qed.
Lemma lem5439474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439475 (_70507 : int) : (term399 _70507) = (term399 _70507).
Proof. exact (MK_COMB (@lem5439474) (@lem5439100 _70507)). Qed.
Lemma lem5439476 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) : (term619 _70504 _70505 _70507 _70508 _70506) = (term620 _70504 _70505 _70507 _70506 _70508).
Proof. exact (MK_COMB (@lem5439475 _70507) (@lem5439473 _70504 _70505 _70507 _70506 _70508)). Qed.
Lemma lem5439477 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439478 (_70506 : int) : (term399 _70506) = (term399 _70506).
Proof. exact (MK_COMB (@lem5439477) (@lem5439052 _70506)). Qed.
Lemma lem5439479 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) : (term621 _70504 _70505 _70507 _70508 _70506) = (term622 _70504 _70505 _70507 _70506 _70508).
Proof. exact (MK_COMB (@lem5439478 _70506) (@lem5439476 _70504 _70505 _70507 _70506 _70508)). Qed.
Lemma lem5439480 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439481 (_70505 : int) : (term399 _70505) = (term399 _70505).
Proof. exact (MK_COMB (@lem5439480) (@lem5439004 _70505)). Qed.
Lemma lem5439482 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) : (term623 _70504 _70505 _70507 _70508 _70506) = (term624 _70504 _70505 _70507 _70506 _70508).
Proof. exact (MK_COMB (@lem5439481 _70505) (@lem5439479 _70504 _70505 _70507 _70506 _70508)). Qed.
Lemma lem5439483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439484 (_70504 : int) : (term399 _70504) = (term399 _70504).
Proof. exact (MK_COMB (@lem5439483) (@lem5438956 _70504)). Qed.
Lemma lem5439485 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) : (term585 _70504 _70505 _70507 _70508 _70506) = (term625 _70504 _70505 _70507 _70506 _70508).
Proof. exact (MK_COMB (@lem5439484 _70504) (@lem5439482 _70504 _70505 _70507 _70506 _70508)). Qed.
Lemma lem5439486 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439487 (_70504 : int) (_70506 : int) : (term586 _70506 _70504) = (term369 _70504 _70506).
Proof. exact (MK_COMB (@lem5439486) (@lem5438908 _70504 _70506)). Qed.
Lemma lem5439488 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) : (term588 _70504 _70505 _70507 _70508 _70506) = (term626 _70504 _70505 _70507 _70506 _70508).
Proof. exact (MK_COMB (@lem5439487 _70504 _70506) (@lem5439485 _70504 _70505 _70507 _70506 _70508)). Qed.
Lemma lem5439489 (_70504 : int) (_70506 : int) : (term627 _70504 _70506) = (term628 _70504 _70506).
Proof. exact (@lem1988289 (real_of_int _70504) (real_of_int _70506)). Qed.
Lemma lem5439502 (_70504 : int) (_70506 : int) : (term361 _70504 _70506) = (term362 _70504 _70506).
Proof. exact (@lem1982792 (real_of_int _70504) (real_of_int _70506)). Qed.
Lemma lem5439503 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5439504 (_70504 : int) (_70506 : int) : (term629 _70504 _70506) = (term630 _70504 _70506).
Proof. exact (MK_COMB (@lem5439503) (@lem5439502 _70504 _70506)). Qed.
Lemma lem5439505 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5439506 (_70504 : int) (_70506 : int) : (term628 _70504 _70506) = (term631 _70504 _70506).
Proof. exact (MK_COMB (@lem5439504 _70504 _70506) (@lem5439505)). Qed.
Lemma lem5439507 (_70504 : int) (_70506 : int) : (term627 _70504 _70506) = (term631 _70504 _70506).
Proof. exact (TRANS (@lem5439489 _70504 _70506) (@lem5439506 _70504 _70506)). Qed.
Lemma lem5439508 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439509 (_70504 : int) (_70508 : int) : (term369 _70504 _70508) = (term369 _70504 _70508).
Proof. exact (MK_COMB (@lem5439508) (@lem5439208 _70504 _70508)). Qed.
Lemma lem5439510 (_70504 : int) (_70505 : int) (_70508 : int) : (term370 _70504 _70505 _70508) = (term370 _70504 _70505 _70508).
Proof. exact (MK_COMB (@lem5439509 _70504 _70508) (@lem5439268 _70505 _70508)). Qed.
Lemma lem5439511 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439512 (_70506 : int) (_70508 : int) : (term369 _70506 _70508) = (term369 _70506 _70508).
Proof. exact (MK_COMB (@lem5439511) (@lem5439331 _70506 _70508)). Qed.
Lemma lem5439513 (_70506 : int) (_70507 : int) (_70508 : int) : (term370 _70506 _70507 _70508) = (term370 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5439512 _70506 _70508) (@lem5439391 _70507 _70508)). Qed.
Lemma lem5439514 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439515 (_70504 : int) (_70505 : int) (_70508 : int) : (term371 _70504 _70505 _70508) = (term371 _70504 _70505 _70508).
Proof. exact (MK_COMB (@lem5439514) (@lem5439510 _70504 _70505 _70508)). Qed.
Lemma lem5439516 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) : (term372 _70504 _70505 _70506 _70507 _70508) = (term372 _70504 _70505 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5439515 _70504 _70505 _70508) (@lem5439513 _70506 _70507 _70508)). Qed.
Lemma lem5439517 (_70508 : int) (_70504 : int) : (term338 _70508 _70504) = (term606 _70508 _70504).
Proof. exact (@lem1988291 (term335 _70508 _70504) term214). Qed.
Lemma lem5439518 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5439541 (_70504 : int) (_70508 : int) : (term335 _70508 _70504) = (term331 _70504 _70508).
Proof. exact (@lem1982757 (real_of_int _70504) (term336 _70508) term294). Qed.
Lemma lem5439542 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem5439543 (_70504 : int) (_70508 : int) : (term607 _70508 _70504) = (term608 _70504 _70508).
Proof. exact (MK_COMB (@lem5439542) (@lem5439541 _70504 _70508)). Qed.
Lemma lem5439544 (_70504 : int) (_70508 : int) : (term609 _70508 _70504) = (term610 _70504 _70508).
Proof. exact (MK_COMB (@lem5439543 _70504 _70508) (@lem5439518)). Qed.
Lemma lem5439545 (_70504 : int) (_70508 : int) : (term610 _70504 _70508) = (term611 _70504 _70508).
Proof. exact (@lem1982792 (term331 _70504 _70508) term214). Qed.
Lemma lem5439547 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5439548 : term214 = term291.
Proof. exact (@lem5439547 (NUMERAL 0)). Qed.
Lemma lem5439550 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5439551 : term294 = term295.
Proof. exact (@lem5439550 term228). Qed.
Lemma lem5439552 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5439553 : term296 = term297.
Proof. exact (MK_COMB (@lem5439552) (@lem5439551)). Qed.
Lemma lem5439554 : term298 = term299.
Proof. exact (MK_COMB (@lem5439553) (@lem5439548)). Qed.
Lemma lem5439555 : term299 = term300.
Proof. exact (@lem1981613 term294 term214 term227 term227). Qed.
Lemma lem5439557 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5439558 : term303 = term304.
Proof. exact (@lem5439557 term228 term228). Qed.
Lemma lem5439559 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5439560 : term306 = term228.
Proof. exact (EQ_MP (@lem5439559) (@lem940073)). Qed.
Lemma lem5439561 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5439562 : term304 = term227.
Proof. exact (MK_COMB (@lem5439561) (@lem5439560)). Qed.
Lemma lem5439563 : term303 = term227.
Proof. exact (TRANS (@lem5439558) (@lem5439562)). Qed.
Lemma lem5439565 (x : nat) : (term307 x) = term214.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5439566 : term298 = term214.
Proof. exact (@lem5439565 term228). Qed.
Lemma lem5439567 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5439568 : term308 = term309.
Proof. exact (MK_COMB (@lem5439567) (@lem5439566)). Qed.
Lemma lem5439569 : term300 = term291.
Proof. exact (MK_COMB (@lem5439568) (@lem5439563)). Qed.
Lemma lem5439570 : term299 = term291.
Proof. exact (TRANS (@lem5439555) (@lem5439569)). Qed.
Lemma lem5439571 : term298 = term291.
Proof. exact (TRANS (@lem5439554) (@lem5439570)). Qed.
Lemma lem5439573 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5439574 : term291 = term214.
Proof. exact (@lem5439573 term214). Qed.
Lemma lem5439575 : term298 = term214.
Proof. exact (TRANS (@lem5439571) (@lem5439574)). Qed.
Lemma lem5439576 (_70504 : int) (_70508 : int) : (term612 _70504 _70508) = (term612 _70504 _70508).
Proof. exact (eq_refl (term612 _70504 _70508)). Qed.
Lemma lem5439577 (_70504 : int) (_70508 : int) : (term611 _70504 _70508) = (term613 _70504 _70508).
Proof. exact (MK_COMB (@lem5439576 _70504 _70508) (@lem5439575)). Qed.
Lemma lem5439578 (_70504 : int) (_70508 : int) : (term613 _70504 _70508) = (term331 _70504 _70508).
Proof. exact (@lem1982723 (term331 _70504 _70508)). Qed.
Lemma lem5439579 (_70504 : int) (_70508 : int) : (term611 _70504 _70508) = (term331 _70504 _70508).
Proof. exact (TRANS (@lem5439577 _70504 _70508) (@lem5439578 _70504 _70508)). Qed.
Lemma lem5439580 (_70504 : int) (_70508 : int) : (term610 _70504 _70508) = (term331 _70504 _70508).
Proof. exact (TRANS (@lem5439545 _70504 _70508) (@lem5439579 _70504 _70508)). Qed.
Lemma lem5439581 (_70504 : int) (_70508 : int) : (term609 _70508 _70504) = (term331 _70504 _70508).
Proof. exact (TRANS (@lem5439544 _70504 _70508) (@lem5439580 _70504 _70508)). Qed.
Lemma lem5439582 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5439583 (_70504 : int) (_70508 : int) : (term614 _70508 _70504) = (term333 _70504 _70508).
Proof. exact (MK_COMB (@lem5439582) (@lem5439581 _70504 _70508)). Qed.
Lemma lem5439584 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5439585 (_70504 : int) (_70508 : int) : (term606 _70508 _70504) = (term334 _70504 _70508).
Proof. exact (MK_COMB (@lem5439583 _70504 _70508) (@lem5439584)). Qed.
Lemma lem5439586 (_70504 : int) (_70508 : int) : (term338 _70508 _70504) = (term334 _70504 _70508).
Proof. exact (TRANS (@lem5439517 _70508 _70504) (@lem5439585 _70504 _70508)). Qed.
Lemma lem5439587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439588 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) : (term395 _70504 _70505 _70506 _70507 _70508) = (term395 _70504 _70505 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5439587) (@lem5439516 _70504 _70505 _70506 _70507 _70508)). Qed.
Lemma lem5439589 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) : (term632 _70505 _70506 _70507 _70508 _70504) = (term633 _70505 _70506 _70507 _70504 _70508).
Proof. exact (MK_COMB (@lem5439588 _70504 _70505 _70506 _70507 _70508) (@lem5439586 _70504 _70508)). Qed.
Lemma lem5439590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439591 (_70508 : int) : (term399 _70508) = (term399 _70508).
Proof. exact (MK_COMB (@lem5439590) (@lem5439148 _70508)). Qed.
Lemma lem5439592 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) : (term634 _70505 _70506 _70507 _70508 _70504) = (term635 _70505 _70506 _70507 _70504 _70508).
Proof. exact (MK_COMB (@lem5439591 _70508) (@lem5439589 _70505 _70506 _70507 _70504 _70508)). Qed.
Lemma lem5439593 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439594 (_70507 : int) : (term399 _70507) = (term399 _70507).
Proof. exact (MK_COMB (@lem5439593) (@lem5439100 _70507)). Qed.
Lemma lem5439595 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) : (term636 _70505 _70506 _70507 _70508 _70504) = (term637 _70505 _70506 _70507 _70504 _70508).
Proof. exact (MK_COMB (@lem5439594 _70507) (@lem5439592 _70505 _70506 _70507 _70504 _70508)). Qed.
Lemma lem5439596 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439597 (_70506 : int) : (term399 _70506) = (term399 _70506).
Proof. exact (MK_COMB (@lem5439596) (@lem5439052 _70506)). Qed.
Lemma lem5439598 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) : (term638 _70505 _70506 _70507 _70508 _70504) = (term639 _70505 _70506 _70507 _70504 _70508).
Proof. exact (MK_COMB (@lem5439597 _70506) (@lem5439595 _70505 _70506 _70507 _70504 _70508)). Qed.
Lemma lem5439599 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439600 (_70505 : int) : (term399 _70505) = (term399 _70505).
Proof. exact (MK_COMB (@lem5439599) (@lem5439004 _70505)). Qed.
Lemma lem5439601 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) : (term640 _70505 _70506 _70507 _70508 _70504) = (term641 _70505 _70506 _70507 _70504 _70508).
Proof. exact (MK_COMB (@lem5439600 _70505) (@lem5439598 _70505 _70506 _70507 _70504 _70508)). Qed.
Lemma lem5439602 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439603 (_70504 : int) : (term399 _70504) = (term399 _70504).
Proof. exact (MK_COMB (@lem5439602) (@lem5438956 _70504)). Qed.
Lemma lem5439604 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) : (term580 _70505 _70506 _70507 _70508 _70504) = (term642 _70505 _70506 _70507 _70504 _70508).
Proof. exact (MK_COMB (@lem5439603 _70504) (@lem5439601 _70505 _70506 _70507 _70504 _70508)). Qed.
Lemma lem5439605 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439606 (_70504 : int) (_70506 : int) : (term581 _70504 _70506) = (term643 _70504 _70506).
Proof. exact (MK_COMB (@lem5439605) (@lem5439507 _70504 _70506)). Qed.
Lemma lem5439607 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) : (term583 _70505 _70506 _70507 _70508 _70504) = (term644 _70505 _70506 _70507 _70504 _70508).
Proof. exact (MK_COMB (@lem5439606 _70504 _70506) (@lem5439604 _70505 _70506 _70507 _70504 _70508)). Qed.
Lemma lem5439608 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5439609 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) : (term590 _70504 _70505 _70507 _70508 _70506) = (term645 _70504 _70505 _70507 _70506 _70508).
Proof. exact (MK_COMB (@lem5439608) (@lem5439488 _70504 _70505 _70507 _70506 _70508)). Qed.
Lemma lem5439610 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) : (term591 _70505 _70506 _70507 _70508 _70504) = (term646 _70505 _70506 _70507 _70504 _70508).
Proof. exact (MK_COMB (@lem5439609 _70504 _70505 _70507 _70506 _70508) (@lem5439607 _70505 _70506 _70507 _70504 _70508)). Qed.
Lemma lem5439622 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) : (term576 _70505 _70507 _70508 _70504 _70506) = (term646 _70505 _70506 _70507 _70504 _70508).
Proof. exact (TRANS (@lem5438889 _70505 _70506 _70507 _70508 _70504) (@lem5439610 _70505 _70506 _70507 _70504 _70508)). Qed.
Lemma lem5439624 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term647 _70504 _70506 _70508 _70505 _70507) = (term648 _70504 _70506 _70508 _70505 _70507).
Proof. exact (eq_refl (term647 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5439625 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term648 _70504 _70506 _70508 _70505 _70507) = (term647 _70504 _70506 _70508 _70505 _70507).
Proof. exact (SYM (@lem5439624 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5439626 (_70504 : int) (_70505 : int) (_70506 : int) (_70508 : int) (_70507 : int) : (term647 _70504 _70506 _70508 _70505 _70507) = (term649 _70504 _70505 _70506 _70508 _70507).
Proof. exact (@lem1483429 (real_of_int _70505) (term650 _70504 _70505 _70506 _70507 _70508) (real_of_int _70507)). Qed.
Lemma lem5439627 (_70504 : int) (_70505 : int) (_70506 : int) (_70508 : int) (_70507 : int) : (term648 _70504 _70506 _70508 _70505 _70507) = (term649 _70504 _70505 _70506 _70508 _70507).
Proof. exact (TRANS (@lem5439625 _70504 _70506 _70508 _70505 _70507) (@lem5439626 _70504 _70505 _70506 _70508 _70507)). Qed.
Lemma lem5439628 (_70504 : int) (_70505 : int) (_70506 : int) (_70508 : int) (_70507 : int) : (term651 _70504 _70505 _70506 _70508 _70507) = (term652 _70504 _70505 _70506 _70508 _70507).
Proof. exact (eq_refl (term651 _70504 _70505 _70506 _70508 _70507)). Qed.
Lemma lem5439629 (_70505 : int) (_70507 : int) : (term581 _70505 _70507) = (term581 _70505 _70507).
Proof. exact (eq_refl (term581 _70505 _70507)). Qed.
Lemma lem5439630 (_70504 : int) (_70505 : int) (_70506 : int) (_70508 : int) (_70507 : int) : (term653 _70504 _70505 _70506 _70508 _70507) = (term654 _70504 _70505 _70506 _70508 _70507).
Proof. exact (MK_COMB (@lem5439629 _70505 _70507) (@lem5439628 _70504 _70505 _70506 _70508 _70507)). Qed.
Lemma lem5439631 (_70504 : int) (_70506 : int) (_70507 : int) (_70508 : int) (_70505 : int) : (term655 _70504 _70506 _70507 _70508 _70505) = (term656 _70504 _70506 _70507 _70508 _70505).
Proof. exact (eq_refl (term655 _70504 _70506 _70507 _70508 _70505)). Qed.
Lemma lem5439632 (_70507 : int) (_70505 : int) : (term586 _70507 _70505) = (term586 _70507 _70505).
Proof. exact (eq_refl (term586 _70507 _70505)). Qed.
Lemma lem5439633 (_70504 : int) (_70506 : int) (_70507 : int) (_70508 : int) (_70505 : int) : (term657 _70504 _70506 _70507 _70508 _70505) = (term658 _70504 _70506 _70507 _70508 _70505).
Proof. exact (MK_COMB (@lem5439632 _70507 _70505) (@lem5439631 _70504 _70506 _70507 _70508 _70505)). Qed.
Lemma lem5439634 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5439635 (_70504 : int) (_70506 : int) (_70507 : int) (_70508 : int) (_70505 : int) : (term659 _70504 _70506 _70507 _70508 _70505) = (term660 _70504 _70506 _70507 _70508 _70505).
Proof. exact (MK_COMB (@lem5439634) (@lem5439633 _70504 _70506 _70507 _70508 _70505)). Qed.
Lemma lem5439636 (_70504 : int) (_70505 : int) (_70506 : int) (_70508 : int) (_70507 : int) : (term649 _70504 _70505 _70506 _70508 _70507) = (term661 _70504 _70505 _70506 _70508 _70507).
Proof. exact (MK_COMB (@lem5439635 _70504 _70506 _70507 _70508 _70505) (@lem5439630 _70504 _70505 _70506 _70508 _70507)). Qed.
Lemma lem5439637 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term662 _70504 _70506 _70508 _70505 _70507) = (term662 _70504 _70506 _70508 _70505 _70507).
Proof. exact (eq_refl (term662 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5439638 (_70504 : int) (_70505 : int) (_70506 : int) (_70508 : int) (_70507 : int) : ((term648 _70504 _70506 _70508 _70505 _70507) = (term649 _70504 _70505 _70506 _70508 _70507)) = ((term648 _70504 _70506 _70508 _70505 _70507) = (term661 _70504 _70505 _70506 _70508 _70507)).
Proof. exact (MK_COMB (@lem5439637 _70504 _70506 _70508 _70505 _70507) (@lem5439636 _70504 _70505 _70506 _70508 _70507)). Qed.
Lemma lem5439639 (_70504 : int) (_70505 : int) (_70506 : int) (_70508 : int) (_70507 : int) : (term648 _70504 _70506 _70508 _70505 _70507) = (term661 _70504 _70505 _70506 _70508 _70507).
Proof. exact (EQ_MP (@lem5439638 _70504 _70505 _70506 _70508 _70507) (@lem5439627 _70504 _70505 _70506 _70508 _70507)). Qed.
Lemma lem5439640 (_70507 : int) (_70505 : int) : (term593 _70507 _70505) = (term360 _70507 _70505).
Proof. exact (@lem1988291 (real_of_int _70507) (real_of_int _70505)). Qed.
Lemma lem5439646 (_70507 : int) (_70505 : int) : (term361 _70507 _70505) = (term362 _70507 _70505).
Proof. exact (@lem1982792 (real_of_int _70507) (real_of_int _70505)). Qed.
Lemma lem5439651 (_70505 : int) (_70507 : int) : (term362 _70507 _70505) = (term363 _70505 _70507).
Proof. exact (@lem1982761 (term336 _70505) (real_of_int _70507)). Qed.
Lemma lem5439653 (_70505 : int) (_70507 : int) : (term361 _70507 _70505) = (term363 _70505 _70507).
Proof. exact (TRANS (@lem5439646 _70507 _70505) (@lem5439651 _70505 _70507)). Qed.
Lemma lem5439654 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5439655 (_70505 : int) (_70507 : int) : (term364 _70507 _70505) = (term365 _70505 _70507).
Proof. exact (MK_COMB (@lem5439654) (@lem5439653 _70505 _70507)). Qed.
Lemma lem5439656 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5439657 (_70505 : int) (_70507 : int) : (term360 _70507 _70505) = (term366 _70505 _70507).
Proof. exact (MK_COMB (@lem5439655 _70505 _70507) (@lem5439656)). Qed.
Lemma lem5439658 (_70505 : int) (_70507 : int) : (term593 _70507 _70505) = (term366 _70505 _70507).
Proof. exact (TRANS (@lem5439640 _70507 _70505) (@lem5439657 _70505 _70507)). Qed.
Lemma lem5439659 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439660 (_70504 : int) (_70508 : int) : (term369 _70504 _70508) = (term369 _70504 _70508).
Proof. exact (MK_COMB (@lem5439659) (@lem5439208 _70504 _70508)). Qed.
Lemma lem5439661 (_70504 : int) (_70505 : int) (_70508 : int) : (term370 _70504 _70505 _70508) = (term370 _70504 _70505 _70508).
Proof. exact (MK_COMB (@lem5439660 _70504 _70508) (@lem5439268 _70505 _70508)). Qed.
Lemma lem5439662 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439663 (_70506 : int) (_70508 : int) : (term369 _70506 _70508) = (term369 _70506 _70508).
Proof. exact (MK_COMB (@lem5439662) (@lem5439331 _70506 _70508)). Qed.
Lemma lem5439664 (_70506 : int) (_70507 : int) (_70508 : int) : (term370 _70506 _70507 _70508) = (term370 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5439663 _70506 _70508) (@lem5439391 _70507 _70508)). Qed.
Lemma lem5439665 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439666 (_70504 : int) (_70505 : int) (_70508 : int) : (term371 _70504 _70505 _70508) = (term371 _70504 _70505 _70508).
Proof. exact (MK_COMB (@lem5439665) (@lem5439661 _70504 _70505 _70508)). Qed.
Lemma lem5439667 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) : (term372 _70504 _70505 _70506 _70507 _70508) = (term372 _70504 _70505 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5439666 _70504 _70505 _70508) (@lem5439664 _70506 _70507 _70508)). Qed.
Lemma lem5439668 (_70508 : int) (_70505 : int) : (term334 _70508 _70505) = (term663 _70508 _70505).
Proof. exact (@lem1988291 (term331 _70508 _70505) term214). Qed.
Lemma lem5439669 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5439692 (_70505 : int) (_70508 : int) : (term331 _70508 _70505) = (term335 _70505 _70508).
Proof. exact (@lem1982757 (term336 _70505) (real_of_int _70508) term294). Qed.
Lemma lem5439693 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem5439694 (_70505 : int) (_70508 : int) : (term608 _70508 _70505) = (term607 _70505 _70508).
Proof. exact (MK_COMB (@lem5439693) (@lem5439692 _70505 _70508)). Qed.
Lemma lem5439695 (_70505 : int) (_70508 : int) : (term610 _70508 _70505) = (term609 _70505 _70508).
Proof. exact (MK_COMB (@lem5439694 _70505 _70508) (@lem5439669)). Qed.
Lemma lem5439696 (_70505 : int) (_70508 : int) : (term609 _70505 _70508) = (term664 _70505 _70508).
Proof. exact (@lem1982792 (term335 _70505 _70508) term214). Qed.
Lemma lem5439698 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5439699 : term214 = term291.
Proof. exact (@lem5439698 (NUMERAL 0)). Qed.
Lemma lem5439701 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5439702 : term294 = term295.
Proof. exact (@lem5439701 term228). Qed.
Lemma lem5439703 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5439704 : term296 = term297.
Proof. exact (MK_COMB (@lem5439703) (@lem5439702)). Qed.
Lemma lem5439705 : term298 = term299.
Proof. exact (MK_COMB (@lem5439704) (@lem5439699)). Qed.
Lemma lem5439706 : term299 = term300.
Proof. exact (@lem1981613 term294 term214 term227 term227). Qed.
Lemma lem5439708 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5439709 : term303 = term304.
Proof. exact (@lem5439708 term228 term228). Qed.
Lemma lem5439710 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5439711 : term306 = term228.
Proof. exact (EQ_MP (@lem5439710) (@lem940073)). Qed.
Lemma lem5439712 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5439713 : term304 = term227.
Proof. exact (MK_COMB (@lem5439712) (@lem5439711)). Qed.
Lemma lem5439714 : term303 = term227.
Proof. exact (TRANS (@lem5439709) (@lem5439713)). Qed.
Lemma lem5439716 (x : nat) : (term307 x) = term214.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5439717 : term298 = term214.
Proof. exact (@lem5439716 term228). Qed.
Lemma lem5439718 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5439719 : term308 = term309.
Proof. exact (MK_COMB (@lem5439718) (@lem5439717)). Qed.
Lemma lem5439720 : term300 = term291.
Proof. exact (MK_COMB (@lem5439719) (@lem5439714)). Qed.
Lemma lem5439721 : term299 = term291.
Proof. exact (TRANS (@lem5439706) (@lem5439720)). Qed.
Lemma lem5439722 : term298 = term291.
Proof. exact (TRANS (@lem5439705) (@lem5439721)). Qed.
Lemma lem5439724 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5439725 : term291 = term214.
Proof. exact (@lem5439724 term214). Qed.
Lemma lem5439726 : term298 = term214.
Proof. exact (TRANS (@lem5439722) (@lem5439725)). Qed.
Lemma lem5439727 (_70505 : int) (_70508 : int) : (term665 _70505 _70508) = (term665 _70505 _70508).
Proof. exact (eq_refl (term665 _70505 _70508)). Qed.
Lemma lem5439728 (_70505 : int) (_70508 : int) : (term664 _70505 _70508) = (term666 _70505 _70508).
Proof. exact (MK_COMB (@lem5439727 _70505 _70508) (@lem5439726)). Qed.
Lemma lem5439729 (_70505 : int) (_70508 : int) : (term666 _70505 _70508) = (term335 _70505 _70508).
Proof. exact (@lem1982723 (term335 _70505 _70508)). Qed.
Lemma lem5439730 (_70505 : int) (_70508 : int) : (term664 _70505 _70508) = (term335 _70505 _70508).
Proof. exact (TRANS (@lem5439728 _70505 _70508) (@lem5439729 _70505 _70508)). Qed.
Lemma lem5439731 (_70505 : int) (_70508 : int) : (term609 _70505 _70508) = (term335 _70505 _70508).
Proof. exact (TRANS (@lem5439696 _70505 _70508) (@lem5439730 _70505 _70508)). Qed.
Lemma lem5439732 (_70505 : int) (_70508 : int) : (term610 _70508 _70505) = (term335 _70505 _70508).
Proof. exact (TRANS (@lem5439695 _70505 _70508) (@lem5439731 _70505 _70508)). Qed.
Lemma lem5439733 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5439734 (_70505 : int) (_70508 : int) : (term667 _70508 _70505) = (term337 _70505 _70508).
Proof. exact (MK_COMB (@lem5439733) (@lem5439732 _70505 _70508)). Qed.
Lemma lem5439735 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5439736 (_70505 : int) (_70508 : int) : (term663 _70508 _70505) = (term338 _70505 _70508).
Proof. exact (MK_COMB (@lem5439734 _70505 _70508) (@lem5439735)). Qed.
Lemma lem5439737 (_70505 : int) (_70508 : int) : (term334 _70508 _70505) = (term338 _70505 _70508).
Proof. exact (TRANS (@lem5439668 _70508 _70505) (@lem5439736 _70505 _70508)). Qed.
Lemma lem5439738 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439739 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) : (term395 _70504 _70505 _70506 _70507 _70508) = (term395 _70504 _70505 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5439738) (@lem5439667 _70504 _70505 _70506 _70507 _70508)). Qed.
Lemma lem5439740 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) : (term668 _70504 _70506 _70507 _70508 _70505) = (term669 _70504 _70506 _70507 _70505 _70508).
Proof. exact (MK_COMB (@lem5439739 _70504 _70505 _70506 _70507 _70508) (@lem5439737 _70505 _70508)). Qed.
Lemma lem5439741 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439742 (_70508 : int) : (term399 _70508) = (term399 _70508).
Proof. exact (MK_COMB (@lem5439741) (@lem5439148 _70508)). Qed.
Lemma lem5439743 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) : (term670 _70504 _70506 _70507 _70508 _70505) = (term671 _70504 _70506 _70507 _70505 _70508).
Proof. exact (MK_COMB (@lem5439742 _70508) (@lem5439740 _70504 _70506 _70507 _70505 _70508)). Qed.
Lemma lem5439744 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439745 (_70507 : int) : (term399 _70507) = (term399 _70507).
Proof. exact (MK_COMB (@lem5439744) (@lem5439100 _70507)). Qed.
Lemma lem5439746 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) : (term672 _70504 _70506 _70507 _70508 _70505) = (term673 _70504 _70506 _70507 _70505 _70508).
Proof. exact (MK_COMB (@lem5439745 _70507) (@lem5439743 _70504 _70506 _70507 _70505 _70508)). Qed.
Lemma lem5439747 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439748 (_70506 : int) : (term399 _70506) = (term399 _70506).
Proof. exact (MK_COMB (@lem5439747) (@lem5439052 _70506)). Qed.
Lemma lem5439749 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) : (term674 _70504 _70506 _70507 _70508 _70505) = (term675 _70504 _70506 _70507 _70505 _70508).
Proof. exact (MK_COMB (@lem5439748 _70506) (@lem5439746 _70504 _70506 _70507 _70505 _70508)). Qed.
Lemma lem5439750 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439751 (_70505 : int) : (term399 _70505) = (term399 _70505).
Proof. exact (MK_COMB (@lem5439750) (@lem5439004 _70505)). Qed.
Lemma lem5439752 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) : (term676 _70504 _70506 _70507 _70508 _70505) = (term677 _70504 _70506 _70507 _70505 _70508).
Proof. exact (MK_COMB (@lem5439751 _70505) (@lem5439749 _70504 _70506 _70507 _70505 _70508)). Qed.
Lemma lem5439753 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439754 (_70504 : int) : (term399 _70504) = (term399 _70504).
Proof. exact (MK_COMB (@lem5439753) (@lem5438956 _70504)). Qed.
Lemma lem5439755 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) : (term656 _70504 _70506 _70507 _70508 _70505) = (term678 _70504 _70506 _70507 _70505 _70508).
Proof. exact (MK_COMB (@lem5439754 _70504) (@lem5439752 _70504 _70506 _70507 _70505 _70508)). Qed.
Lemma lem5439756 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439757 (_70505 : int) (_70507 : int) : (term586 _70507 _70505) = (term369 _70505 _70507).
Proof. exact (MK_COMB (@lem5439756) (@lem5439658 _70505 _70507)). Qed.
Lemma lem5439758 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) : (term658 _70504 _70506 _70507 _70508 _70505) = (term679 _70504 _70506 _70507 _70505 _70508).
Proof. exact (MK_COMB (@lem5439757 _70505 _70507) (@lem5439755 _70504 _70506 _70507 _70505 _70508)). Qed.
Lemma lem5439759 (_70505 : int) (_70507 : int) : (term627 _70505 _70507) = (term628 _70505 _70507).
Proof. exact (@lem1988289 (real_of_int _70505) (real_of_int _70507)). Qed.
Lemma lem5439772 (_70505 : int) (_70507 : int) : (term361 _70505 _70507) = (term362 _70505 _70507).
Proof. exact (@lem1982792 (real_of_int _70505) (real_of_int _70507)). Qed.
Lemma lem5439773 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5439774 (_70505 : int) (_70507 : int) : (term629 _70505 _70507) = (term630 _70505 _70507).
Proof. exact (MK_COMB (@lem5439773) (@lem5439772 _70505 _70507)). Qed.
Lemma lem5439775 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5439776 (_70505 : int) (_70507 : int) : (term628 _70505 _70507) = (term631 _70505 _70507).
Proof. exact (MK_COMB (@lem5439774 _70505 _70507) (@lem5439775)). Qed.
Lemma lem5439777 (_70505 : int) (_70507 : int) : (term627 _70505 _70507) = (term631 _70505 _70507).
Proof. exact (TRANS (@lem5439759 _70505 _70507) (@lem5439776 _70505 _70507)). Qed.
Lemma lem5439778 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439779 (_70504 : int) (_70508 : int) : (term369 _70504 _70508) = (term369 _70504 _70508).
Proof. exact (MK_COMB (@lem5439778) (@lem5439208 _70504 _70508)). Qed.
Lemma lem5439780 (_70504 : int) (_70505 : int) (_70508 : int) : (term370 _70504 _70505 _70508) = (term370 _70504 _70505 _70508).
Proof. exact (MK_COMB (@lem5439779 _70504 _70508) (@lem5439268 _70505 _70508)). Qed.
Lemma lem5439781 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439782 (_70506 : int) (_70508 : int) : (term369 _70506 _70508) = (term369 _70506 _70508).
Proof. exact (MK_COMB (@lem5439781) (@lem5439331 _70506 _70508)). Qed.
Lemma lem5439783 (_70506 : int) (_70507 : int) (_70508 : int) : (term370 _70506 _70507 _70508) = (term370 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5439782 _70506 _70508) (@lem5439391 _70507 _70508)). Qed.
Lemma lem5439784 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439785 (_70504 : int) (_70505 : int) (_70508 : int) : (term371 _70504 _70505 _70508) = (term371 _70504 _70505 _70508).
Proof. exact (MK_COMB (@lem5439784) (@lem5439780 _70504 _70505 _70508)). Qed.
Lemma lem5439786 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) : (term372 _70504 _70505 _70506 _70507 _70508) = (term372 _70504 _70505 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5439785 _70504 _70505 _70508) (@lem5439783 _70506 _70507 _70508)). Qed.
Lemma lem5439787 (_70508 : int) (_70507 : int) : (term334 _70508 _70507) = (term663 _70508 _70507).
Proof. exact (@lem1988291 (term331 _70508 _70507) term214). Qed.
Lemma lem5439788 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5439811 (_70507 : int) (_70508 : int) : (term331 _70508 _70507) = (term335 _70507 _70508).
Proof. exact (@lem1982757 (term336 _70507) (real_of_int _70508) term294). Qed.
Lemma lem5439812 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem5439813 (_70507 : int) (_70508 : int) : (term608 _70508 _70507) = (term607 _70507 _70508).
Proof. exact (MK_COMB (@lem5439812) (@lem5439811 _70507 _70508)). Qed.
Lemma lem5439814 (_70507 : int) (_70508 : int) : (term610 _70508 _70507) = (term609 _70507 _70508).
Proof. exact (MK_COMB (@lem5439813 _70507 _70508) (@lem5439788)). Qed.
Lemma lem5439815 (_70507 : int) (_70508 : int) : (term609 _70507 _70508) = (term664 _70507 _70508).
Proof. exact (@lem1982792 (term335 _70507 _70508) term214). Qed.
Lemma lem5439817 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5439818 : term214 = term291.
Proof. exact (@lem5439817 (NUMERAL 0)). Qed.
Lemma lem5439820 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5439821 : term294 = term295.
Proof. exact (@lem5439820 term228). Qed.
Lemma lem5439822 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5439823 : term296 = term297.
Proof. exact (MK_COMB (@lem5439822) (@lem5439821)). Qed.
Lemma lem5439824 : term298 = term299.
Proof. exact (MK_COMB (@lem5439823) (@lem5439818)). Qed.
Lemma lem5439825 : term299 = term300.
Proof. exact (@lem1981613 term294 term214 term227 term227). Qed.
Lemma lem5439827 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5439828 : term303 = term304.
Proof. exact (@lem5439827 term228 term228). Qed.
Lemma lem5439829 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5439830 : term306 = term228.
Proof. exact (EQ_MP (@lem5439829) (@lem940073)). Qed.
Lemma lem5439831 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5439832 : term304 = term227.
Proof. exact (MK_COMB (@lem5439831) (@lem5439830)). Qed.
Lemma lem5439833 : term303 = term227.
Proof. exact (TRANS (@lem5439828) (@lem5439832)). Qed.
Lemma lem5439835 (x : nat) : (term307 x) = term214.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5439836 : term298 = term214.
Proof. exact (@lem5439835 term228). Qed.
Lemma lem5439837 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5439838 : term308 = term309.
Proof. exact (MK_COMB (@lem5439837) (@lem5439836)). Qed.
Lemma lem5439839 : term300 = term291.
Proof. exact (MK_COMB (@lem5439838) (@lem5439833)). Qed.
Lemma lem5439840 : term299 = term291.
Proof. exact (TRANS (@lem5439825) (@lem5439839)). Qed.
Lemma lem5439841 : term298 = term291.
Proof. exact (TRANS (@lem5439824) (@lem5439840)). Qed.
Lemma lem5439843 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5439844 : term291 = term214.
Proof. exact (@lem5439843 term214). Qed.
Lemma lem5439845 : term298 = term214.
Proof. exact (TRANS (@lem5439841) (@lem5439844)). Qed.
Lemma lem5439846 (_70507 : int) (_70508 : int) : (term665 _70507 _70508) = (term665 _70507 _70508).
Proof. exact (eq_refl (term665 _70507 _70508)). Qed.
Lemma lem5439847 (_70507 : int) (_70508 : int) : (term664 _70507 _70508) = (term666 _70507 _70508).
Proof. exact (MK_COMB (@lem5439846 _70507 _70508) (@lem5439845)). Qed.
Lemma lem5439848 (_70507 : int) (_70508 : int) : (term666 _70507 _70508) = (term335 _70507 _70508).
Proof. exact (@lem1982723 (term335 _70507 _70508)). Qed.
Lemma lem5439849 (_70507 : int) (_70508 : int) : (term664 _70507 _70508) = (term335 _70507 _70508).
Proof. exact (TRANS (@lem5439847 _70507 _70508) (@lem5439848 _70507 _70508)). Qed.
Lemma lem5439850 (_70507 : int) (_70508 : int) : (term609 _70507 _70508) = (term335 _70507 _70508).
Proof. exact (TRANS (@lem5439815 _70507 _70508) (@lem5439849 _70507 _70508)). Qed.
Lemma lem5439851 (_70507 : int) (_70508 : int) : (term610 _70508 _70507) = (term335 _70507 _70508).
Proof. exact (TRANS (@lem5439814 _70507 _70508) (@lem5439850 _70507 _70508)). Qed.
Lemma lem5439852 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5439853 (_70507 : int) (_70508 : int) : (term667 _70508 _70507) = (term337 _70507 _70508).
Proof. exact (MK_COMB (@lem5439852) (@lem5439851 _70507 _70508)). Qed.
Lemma lem5439854 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5439855 (_70507 : int) (_70508 : int) : (term663 _70508 _70507) = (term338 _70507 _70508).
Proof. exact (MK_COMB (@lem5439853 _70507 _70508) (@lem5439854)). Qed.
Lemma lem5439856 (_70507 : int) (_70508 : int) : (term334 _70508 _70507) = (term338 _70507 _70508).
Proof. exact (TRANS (@lem5439787 _70508 _70507) (@lem5439855 _70507 _70508)). Qed.
Lemma lem5439857 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439858 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) : (term395 _70504 _70505 _70506 _70507 _70508) = (term395 _70504 _70505 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5439857) (@lem5439786 _70504 _70505 _70506 _70507 _70508)). Qed.
Lemma lem5439859 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) : (term680 _70504 _70505 _70506 _70508 _70507) = (term681 _70504 _70505 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5439858 _70504 _70505 _70506 _70507 _70508) (@lem5439856 _70507 _70508)). Qed.
Lemma lem5439860 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439861 (_70508 : int) : (term399 _70508) = (term399 _70508).
Proof. exact (MK_COMB (@lem5439860) (@lem5439148 _70508)). Qed.
Lemma lem5439862 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) : (term682 _70504 _70505 _70506 _70508 _70507) = (term683 _70504 _70505 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5439861 _70508) (@lem5439859 _70504 _70505 _70506 _70507 _70508)). Qed.
Lemma lem5439863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439864 (_70507 : int) : (term399 _70507) = (term399 _70507).
Proof. exact (MK_COMB (@lem5439863) (@lem5439100 _70507)). Qed.
Lemma lem5439865 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) : (term684 _70504 _70505 _70506 _70508 _70507) = (term685 _70504 _70505 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5439864 _70507) (@lem5439862 _70504 _70505 _70506 _70507 _70508)). Qed.
Lemma lem5439866 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439867 (_70506 : int) : (term399 _70506) = (term399 _70506).
Proof. exact (MK_COMB (@lem5439866) (@lem5439052 _70506)). Qed.
Lemma lem5439868 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) : (term686 _70504 _70505 _70506 _70508 _70507) = (term687 _70504 _70505 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5439867 _70506) (@lem5439865 _70504 _70505 _70506 _70507 _70508)). Qed.
Lemma lem5439869 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439870 (_70505 : int) : (term399 _70505) = (term399 _70505).
Proof. exact (MK_COMB (@lem5439869) (@lem5439004 _70505)). Qed.
Lemma lem5439871 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) : (term688 _70504 _70505 _70506 _70508 _70507) = (term689 _70504 _70505 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5439870 _70505) (@lem5439868 _70504 _70505 _70506 _70507 _70508)). Qed.
Lemma lem5439872 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439873 (_70504 : int) : (term399 _70504) = (term399 _70504).
Proof. exact (MK_COMB (@lem5439872) (@lem5438956 _70504)). Qed.
Lemma lem5439874 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) : (term652 _70504 _70505 _70506 _70508 _70507) = (term690 _70504 _70505 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5439873 _70504) (@lem5439871 _70504 _70505 _70506 _70507 _70508)). Qed.
Lemma lem5439875 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5439876 (_70505 : int) (_70507 : int) : (term581 _70505 _70507) = (term643 _70505 _70507).
Proof. exact (MK_COMB (@lem5439875) (@lem5439777 _70505 _70507)). Qed.
Lemma lem5439877 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) : (term654 _70504 _70505 _70506 _70508 _70507) = (term691 _70504 _70505 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5439876 _70505 _70507) (@lem5439874 _70504 _70505 _70506 _70507 _70508)). Qed.
Lemma lem5439878 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5439879 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) : (term660 _70504 _70506 _70507 _70508 _70505) = (term692 _70504 _70506 _70507 _70505 _70508).
Proof. exact (MK_COMB (@lem5439878) (@lem5439758 _70504 _70506 _70507 _70505 _70508)). Qed.
Lemma lem5439880 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) : (term661 _70504 _70505 _70506 _70508 _70507) = (term693 _70504 _70505 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5439879 _70504 _70506 _70507 _70505 _70508) (@lem5439877 _70504 _70505 _70506 _70507 _70508)). Qed.
Lemma lem5439892 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) : (term648 _70504 _70506 _70508 _70505 _70507) = (term693 _70504 _70505 _70506 _70507 _70508).
Proof. exact (TRANS (@lem5439639 _70504 _70505 _70506 _70508 _70507) (@lem5439880 _70504 _70505 _70506 _70507 _70508)). Qed.
Lemma lem5439893 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5439894 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) : (term694 _70505 _70507 _70508 _70504 _70506) = (term695 _70505 _70506 _70507 _70504 _70508).
Proof. exact (MK_COMB (@lem5439893) (@lem5439622 _70505 _70506 _70507 _70504 _70508)). Qed.
Lemma lem5439895 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) : (term507 _70504 _70506 _70508 _70505 _70507) = (term696 _70504 _70505 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5439894 _70505 _70506 _70507 _70504 _70508) (@lem5439892 _70504 _70505 _70506 _70507 _70508)). Qed.
Lemma lem5439896 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5439897 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : (term524 _70504 _70506 _70508 _70505 _70507) = (term697 _70504 _70506 _70505 _70507 _70508).
Proof. exact (MK_COMB (@lem5439896) (@lem5438872 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5439898 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) : (term525 _70504 _70506 _70508 _70505 _70507) = (term698 _70504 _70505 _70506 _70507 _70508).
Proof. exact (MK_COMB (@lem5439897 _70504 _70506 _70505 _70507 _70508) (@lem5439895 _70504 _70505 _70506 _70507 _70508)). Qed.
Lemma lem5439899 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term698 _70504 _70505 _70506 _70507 _70508) : term698 _70504 _70505 _70506 _70507 _70508.
Proof. exact (h1). Qed.
Lemma lem5439900 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term574 _70504 _70506 _70505 _70507 _70508) : term574 _70504 _70506 _70505 _70507 _70508.
Proof. exact (h1). Qed.
Lemma lem5439901 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term555 _70504 _70506 _70505 _70507 _70508) : term555 _70504 _70506 _70505 _70507 _70508.
Proof. exact (h1). Qed.
Lemma lem5439902 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term544 _70504 _70506 _70505 _70507 _70508) : term544 _70504 _70506 _70505 _70507 _70508.
Proof. exact (h1). Qed.
Lemma lem5439903 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term544 _70504 _70506 _70505 _70507 _70508) : term542 _70504 _70506 _70505 _70507 _70508.
Proof. exact (proj2 (@lem5439902 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5439905 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term544 _70504 _70506 _70505 _70507 _70508) : term541 _70504 _70506 _70505 _70507 _70508.
Proof. exact (proj2 (@lem5439903 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5439907 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term544 _70504 _70506 _70505 _70507 _70508) : term540 _70504 _70506 _70505 _70507 _70508.
Proof. exact (proj2 (@lem5439905 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5439909 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term544 _70504 _70506 _70505 _70507 _70508) : term539 _70504 _70506 _70505 _70507 _70508.
Proof. exact (proj2 (@lem5439907 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5439911 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term544 _70504 _70506 _70505 _70507 _70508) : term538 _70504 _70506 _70505 _70507 _70508.
Proof. exact (proj2 (@lem5439909 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5439913 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term544 _70504 _70506 _70505 _70507 _70508) : term536 _70504 _70506 _70505 _70507 _70508.
Proof. exact (proj2 (@lem5439911 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5439914 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term544 _70504 _70506 _70505 _70507 _70508) : term334 _70504 _70508.
Proof. exact (proj1 (@lem5439911 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5439916 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term544 _70504 _70506 _70505 _70507 _70508) : term530 _70504 _70506 _70508.
Proof. exact (proj1 (@lem5439913 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5439918 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term544 _70504 _70506 _70505 _70507 _70508) : term366 _70504 _70508.
Proof. exact (proj1 (@lem5439916 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5439922 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5439923 : term699 = term700.
Proof. exact (@lem5439922 term214 term227). Qed.
Lemma lem5439925 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5439926 : term227 = term320.
Proof. exact (@lem5439925 term228). Qed.
Lemma lem5439928 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5439929 : term214 = term291.
Proof. exact (@lem5439928 (NUMERAL 0)). Qed.
Lemma lem5439930 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5439931 : term701 = term702.
Proof. exact (MK_COMB (@lem5439930) (@lem5439929)). Qed.
Lemma lem5439932 : term700 = term703.
Proof. exact (MK_COMB (@lem5439931) (@lem5439926)). Qed.
Lemma lem5439933 : term704.
Proof. exact (@lem1980255 term214 term227 term227 term227). Qed.
Lemma lem5439935 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5439936 : term700 = term706.
Proof. exact (@lem5439935 (NUMERAL 0) term228). Qed.
Lemma lem5439937 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5439938 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5439939 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5439938 h1) (fun h1 : term706 = True => @lem5439937)). Qed.
Lemma lem5439940 : term706 = True.
Proof. exact (EQ_MP (@lem5439939) (@lem5439937)). Qed.
Lemma lem5439941 : term700 = True.
Proof. exact (TRANS (@lem5439936) (@lem5439940)). Qed.
Lemma lem5439942 : True = term700.
Proof. exact (SYM (@lem5439941)). Qed.
Lemma lem5439943 : term700.
Proof. exact (EQ_MP (@lem5439942) (@lem0)). Qed.
Lemma lem5439944 : term708.
Proof. exact (@lem5439933 (@lem5439943)). Qed.
Lemma lem5439946 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5439947 : term700 = term706.
Proof. exact (@lem5439946 (NUMERAL 0) term228). Qed.
Lemma lem5439948 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5439949 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5439950 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5439949 h1) (fun h1 : term706 = True => @lem5439948)). Qed.
Lemma lem5439951 : term706 = True.
Proof. exact (EQ_MP (@lem5439950) (@lem5439948)). Qed.
Lemma lem5439952 : term700 = True.
Proof. exact (TRANS (@lem5439947) (@lem5439951)). Qed.
Lemma lem5439953 : True = term700.
Proof. exact (SYM (@lem5439952)). Qed.
Lemma lem5439954 : term700.
Proof. exact (EQ_MP (@lem5439953) (@lem0)). Qed.
Lemma lem5439955 : term703 = term709.
Proof. exact (@lem5439944 (@lem5439954)). Qed.
Lemma lem5439957 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5439958 : term303 = term304.
Proof. exact (@lem5439957 term228 term228). Qed.
Lemma lem5439959 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5439960 : term306 = term228.
Proof. exact (EQ_MP (@lem5439959) (@lem940073)). Qed.
Lemma lem5439961 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5439962 : term304 = term227.
Proof. exact (MK_COMB (@lem5439961) (@lem5439960)). Qed.
Lemma lem5439963 : term303 = term227.
Proof. exact (TRANS (@lem5439958) (@lem5439962)). Qed.
Lemma lem5439965 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5439966 : term711 = term214.
Proof. exact (@lem5439965 term228). Qed.
Lemma lem5439967 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5439968 : term712 = term701.
Proof. exact (MK_COMB (@lem5439967) (@lem5439966)). Qed.
Lemma lem5439969 : term709 = term700.
Proof. exact (MK_COMB (@lem5439968) (@lem5439963)). Qed.
Lemma lem5439971 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5439972 : term700 = term706.
Proof. exact (@lem5439971 (NUMERAL 0) term228). Qed.
Lemma lem5439973 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5439974 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5439975 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5439974 h1) (fun h1 : term706 = True => @lem5439973)). Qed.
Lemma lem5439976 : term706 = True.
Proof. exact (EQ_MP (@lem5439975) (@lem5439973)). Qed.
Lemma lem5439977 : term700 = True.
Proof. exact (TRANS (@lem5439972) (@lem5439976)). Qed.
Lemma lem5439978 : term709 = True.
Proof. exact (TRANS (@lem5439969) (@lem5439977)). Qed.
Lemma lem5439979 : term703 = True.
Proof. exact (TRANS (@lem5439955) (@lem5439978)). Qed.
Lemma lem5439980 : term700 = True.
Proof. exact (TRANS (@lem5439932) (@lem5439979)). Qed.
Lemma lem5439981 : term699 = True.
Proof. exact (TRANS (@lem5439923) (@lem5439980)). Qed.
Lemma lem5439982 : True = term699.
Proof. exact (SYM (@lem5439981)). Qed.
Lemma lem5439983 : term699.
Proof. exact (EQ_MP (@lem5439982) (@lem0)). Qed.
Lemma lem5439984 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term544 _70504 _70506 _70505 _70507 _70508) : term713 _70504 _70508.
Proof. exact (conj (@lem5439983) (@lem5439914 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5439986 (x : real) (y : real) : term714 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5439987 (_70504 : int) (_70508 : int) : term715 _70504 _70508.
Proof. exact (@lem5439986 term227 (term331 _70504 _70508)). Qed.
Lemma lem5439988 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term544 _70504 _70506 _70505 _70507 _70508) : term716 _70504 _70508.
Proof. exact (@lem5439987 _70504 _70508 (@lem5439984 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5439989 (_70504 : int) (_70508 : int) : (term717 _70504 _70508) = (term331 _70504 _70508).
Proof. exact (@lem1982733 (term331 _70504 _70508)). Qed.
Lemma lem5439990 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5439991 (_70504 : int) (_70508 : int) : (term718 _70504 _70508) = (term333 _70504 _70508).
Proof. exact (MK_COMB (@lem5439990) (@lem5439989 _70504 _70508)). Qed.
Lemma lem5439992 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5439993 (_70504 : int) (_70508 : int) : (term716 _70504 _70508) = (term334 _70504 _70508).
Proof. exact (MK_COMB (@lem5439991 _70504 _70508) (@lem5439992)). Qed.
Lemma lem5439994 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term544 _70504 _70506 _70505 _70507 _70508) : term334 _70504 _70508.
Proof. exact (EQ_MP (@lem5439993 _70504 _70508) (@lem5439988 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5439996 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5439997 : term699 = term700.
Proof. exact (@lem5439996 term214 term227). Qed.
Lemma lem5439999 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5440000 : term227 = term320.
Proof. exact (@lem5439999 term228). Qed.
Lemma lem5440002 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5440003 : term214 = term291.
Proof. exact (@lem5440002 (NUMERAL 0)). Qed.
Lemma lem5440004 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5440005 : term701 = term702.
Proof. exact (MK_COMB (@lem5440004) (@lem5440003)). Qed.
Lemma lem5440006 : term700 = term703.
Proof. exact (MK_COMB (@lem5440005) (@lem5440000)). Qed.
Lemma lem5440007 : term704.
Proof. exact (@lem1980255 term214 term227 term227 term227). Qed.
Lemma lem5440009 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440010 : term700 = term706.
Proof. exact (@lem5440009 (NUMERAL 0) term228). Qed.
Lemma lem5440011 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440012 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440013 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440012 h1) (fun h1 : term706 = True => @lem5440011)). Qed.
Lemma lem5440014 : term706 = True.
Proof. exact (EQ_MP (@lem5440013) (@lem5440011)). Qed.
Lemma lem5440015 : term700 = True.
Proof. exact (TRANS (@lem5440010) (@lem5440014)). Qed.
Lemma lem5440016 : True = term700.
Proof. exact (SYM (@lem5440015)). Qed.
Lemma lem5440017 : term700.
Proof. exact (EQ_MP (@lem5440016) (@lem0)). Qed.
Lemma lem5440018 : term708.
Proof. exact (@lem5440007 (@lem5440017)). Qed.
Lemma lem5440020 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440021 : term700 = term706.
Proof. exact (@lem5440020 (NUMERAL 0) term228). Qed.
Lemma lem5440022 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440023 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440024 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440023 h1) (fun h1 : term706 = True => @lem5440022)). Qed.
Lemma lem5440025 : term706 = True.
Proof. exact (EQ_MP (@lem5440024) (@lem5440022)). Qed.
Lemma lem5440026 : term700 = True.
Proof. exact (TRANS (@lem5440021) (@lem5440025)). Qed.
Lemma lem5440027 : True = term700.
Proof. exact (SYM (@lem5440026)). Qed.
Lemma lem5440028 : term700.
Proof. exact (EQ_MP (@lem5440027) (@lem0)). Qed.
Lemma lem5440029 : term703 = term709.
Proof. exact (@lem5440018 (@lem5440028)). Qed.
Lemma lem5440031 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5440032 : term303 = term304.
Proof. exact (@lem5440031 term228 term228). Qed.
Lemma lem5440033 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5440034 : term306 = term228.
Proof. exact (EQ_MP (@lem5440033) (@lem940073)). Qed.
Lemma lem5440035 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5440036 : term304 = term227.
Proof. exact (MK_COMB (@lem5440035) (@lem5440034)). Qed.
Lemma lem5440037 : term303 = term227.
Proof. exact (TRANS (@lem5440032) (@lem5440036)). Qed.
Lemma lem5440039 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5440040 : term711 = term214.
Proof. exact (@lem5440039 term228). Qed.
Lemma lem5440041 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5440042 : term712 = term701.
Proof. exact (MK_COMB (@lem5440041) (@lem5440040)). Qed.
Lemma lem5440043 : term709 = term700.
Proof. exact (MK_COMB (@lem5440042) (@lem5440037)). Qed.
Lemma lem5440045 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440046 : term700 = term706.
Proof. exact (@lem5440045 (NUMERAL 0) term228). Qed.
Lemma lem5440047 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440048 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440049 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440048 h1) (fun h1 : term706 = True => @lem5440047)). Qed.
Lemma lem5440050 : term706 = True.
Proof. exact (EQ_MP (@lem5440049) (@lem5440047)). Qed.
Lemma lem5440051 : term700 = True.
Proof. exact (TRANS (@lem5440046) (@lem5440050)). Qed.
Lemma lem5440052 : term709 = True.
Proof. exact (TRANS (@lem5440043) (@lem5440051)). Qed.
Lemma lem5440053 : term703 = True.
Proof. exact (TRANS (@lem5440029) (@lem5440052)). Qed.
Lemma lem5440054 : term700 = True.
Proof. exact (TRANS (@lem5440006) (@lem5440053)). Qed.
Lemma lem5440055 : term699 = True.
Proof. exact (TRANS (@lem5439997) (@lem5440054)). Qed.
Lemma lem5440056 : True = term699.
Proof. exact (SYM (@lem5440055)). Qed.
Lemma lem5440057 : term699.
Proof. exact (EQ_MP (@lem5440056) (@lem0)). Qed.
Lemma lem5440058 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term544 _70504 _70506 _70505 _70507 _70508) : term719 _70504 _70508.
Proof. exact (conj (@lem5440057) (@lem5439918 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440060 (x : real) (y : real) : term714 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5440061 (_70504 : int) (_70508 : int) : term720 _70504 _70508.
Proof. exact (@lem5440060 term227 (term363 _70504 _70508)). Qed.
Lemma lem5440062 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term544 _70504 _70506 _70505 _70507 _70508) : term721 _70504 _70508.
Proof. exact (@lem5440061 _70504 _70508 (@lem5440058 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440063 (_70504 : int) (_70508 : int) : (term722 _70504 _70508) = (term363 _70504 _70508).
Proof. exact (@lem1982733 (term363 _70504 _70508)). Qed.
Lemma lem5440064 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5440065 (_70504 : int) (_70508 : int) : (term723 _70504 _70508) = (term365 _70504 _70508).
Proof. exact (MK_COMB (@lem5440064) (@lem5440063 _70504 _70508)). Qed.
Lemma lem5440066 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5440067 (_70504 : int) (_70508 : int) : (term721 _70504 _70508) = (term366 _70504 _70508).
Proof. exact (MK_COMB (@lem5440065 _70504 _70508) (@lem5440066)). Qed.
Lemma lem5440068 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term544 _70504 _70506 _70505 _70507 _70508) : term366 _70504 _70508.
Proof. exact (EQ_MP (@lem5440067 _70504 _70508) (@lem5440062 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440069 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term544 _70504 _70506 _70505 _70507 _70508) : term724 _70504 _70508.
Proof. exact (conj (@lem5440068 _70504 _70506 _70505 _70507 _70508 h1) (@lem5439994 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440071 (x : real) (y : real) : term725 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5440072 (_70504 : int) (_70508 : int) : term726 _70504 _70508.
Proof. exact (@lem5440071 (term363 _70504 _70508) (term331 _70504 _70508)). Qed.
Lemma lem5440073 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term544 _70504 _70506 _70505 _70507 _70508) : term727 _70504 _70508.
Proof. exact (@lem5440072 _70504 _70508 (@lem5440069 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440074 (_70504 : int) (_70508 : int) : (term728 _70504 _70508) = (term729 _70504 _70508).
Proof. exact (@lem1982753 (term336 _70504) (real_of_int _70504) (real_of_int _70508) (term330 _70508)). Qed.
Lemma lem5440075 (_70504 : int) : (term730 _70504) = (term731 _70504).
Proof. exact (@lem1982713 term294 (real_of_int _70504)). Qed.
Lemma lem5440077 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5440078 : term227 = term320.
Proof. exact (@lem5440077 term228). Qed.
Lemma lem5440080 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5440081 : term294 = term295.
Proof. exact (@lem5440080 term228). Qed.
Lemma lem5440082 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5440083 : term732 = term733.
Proof. exact (MK_COMB (@lem5440082) (@lem5440081)). Qed.
Lemma lem5440084 : term734 = term735.
Proof. exact (MK_COMB (@lem5440083) (@lem5440078)). Qed.
Lemma lem5440085 : term736.
Proof. exact (@lem1981473 term294 term227 term227 term227 term214 term227). Qed.
Lemma lem5440087 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440088 : term700 = term706.
Proof. exact (@lem5440087 (NUMERAL 0) term228). Qed.
Lemma lem5440089 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440090 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440091 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440090 h1) (fun h1 : term706 = True => @lem5440089)). Qed.
Lemma lem5440092 : term706 = True.
Proof. exact (EQ_MP (@lem5440091) (@lem5440089)). Qed.
Lemma lem5440093 : term700 = True.
Proof. exact (TRANS (@lem5440088) (@lem5440092)). Qed.
Lemma lem5440094 : True = term700.
Proof. exact (SYM (@lem5440093)). Qed.
Lemma lem5440095 : term700.
Proof. exact (EQ_MP (@lem5440094) (@lem0)). Qed.
Lemma lem5440096 : term737.
Proof. exact (@lem5440085 (@lem5440095)). Qed.
Lemma lem5440098 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440099 : term700 = term706.
Proof. exact (@lem5440098 (NUMERAL 0) term228). Qed.
Lemma lem5440100 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440101 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440102 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440101 h1) (fun h1 : term706 = True => @lem5440100)). Qed.
Lemma lem5440103 : term706 = True.
Proof. exact (EQ_MP (@lem5440102) (@lem5440100)). Qed.
Lemma lem5440104 : term700 = True.
Proof. exact (TRANS (@lem5440099) (@lem5440103)). Qed.
Lemma lem5440105 : True = term700.
Proof. exact (SYM (@lem5440104)). Qed.
Lemma lem5440106 : term700.
Proof. exact (EQ_MP (@lem5440105) (@lem0)). Qed.
Lemma lem5440107 : term738.
Proof. exact (@lem5440096 (@lem5440106)). Qed.
Lemma lem5440109 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440110 : term700 = term706.
Proof. exact (@lem5440109 (NUMERAL 0) term228). Qed.
Lemma lem5440111 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440112 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440113 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440112 h1) (fun h1 : term706 = True => @lem5440111)). Qed.
Lemma lem5440114 : term706 = True.
Proof. exact (EQ_MP (@lem5440113) (@lem5440111)). Qed.
Lemma lem5440115 : term700 = True.
Proof. exact (TRANS (@lem5440110) (@lem5440114)). Qed.
Lemma lem5440116 : True = term700.
Proof. exact (SYM (@lem5440115)). Qed.
Lemma lem5440117 : term700.
Proof. exact (EQ_MP (@lem5440116) (@lem0)). Qed.
Lemma lem5440118 : term739.
Proof. exact (@lem5440107 (@lem5440117)). Qed.
Lemma lem5440120 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5440121 : term303 = term304.
Proof. exact (@lem5440120 term228 term228). Qed.
Lemma lem5440122 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5440123 : term306 = term228.
Proof. exact (EQ_MP (@lem5440122) (@lem940073)). Qed.
Lemma lem5440124 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5440125 : term304 = term227.
Proof. exact (MK_COMB (@lem5440124) (@lem5440123)). Qed.
Lemma lem5440126 : term303 = term227.
Proof. exact (TRANS (@lem5440121) (@lem5440125)). Qed.
Lemma lem5440128 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5440129 : term321 = term326.
Proof. exact (@lem5440128 term228 term228). Qed.
Lemma lem5440130 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5440131 : term306 = term228.
Proof. exact (EQ_MP (@lem5440130) (@lem940073)). Qed.
Lemma lem5440132 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5440133 : term304 = term227.
Proof. exact (MK_COMB (@lem5440132) (@lem5440131)). Qed.
Lemma lem5440134 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5440135 : term326 = term294.
Proof. exact (MK_COMB (@lem5440134) (@lem5440133)). Qed.
Lemma lem5440136 : term321 = term294.
Proof. exact (TRANS (@lem5440129) (@lem5440135)). Qed.
Lemma lem5440137 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5440138 : term740 = term732.
Proof. exact (MK_COMB (@lem5440137) (@lem5440136)). Qed.
Lemma lem5440139 : term741 = term734.
Proof. exact (MK_COMB (@lem5440138) (@lem5440126)). Qed.
Lemma lem5440141 (m : nat) : (term742 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5440142 : term734 = term214.
Proof. exact (@lem5440141 term228). Qed.
Lemma lem5440143 : term741 = term214.
Proof. exact (TRANS (@lem5440139) (@lem5440142)). Qed.
Lemma lem5440144 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5440145 : term743 = term744.
Proof. exact (MK_COMB (@lem5440144) (@lem5440143)). Qed.
Lemma lem5440146 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem5440147 : term745 = term711.
Proof. exact (MK_COMB (@lem5440145) (@lem5440146)). Qed.
Lemma lem5440149 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5440150 : term711 = term214.
Proof. exact (@lem5440149 term228). Qed.
Lemma lem5440151 : term745 = term214.
Proof. exact (TRANS (@lem5440147) (@lem5440150)). Qed.
Lemma lem5440153 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5440154 : term303 = term304.
Proof. exact (@lem5440153 term228 term228). Qed.
Lemma lem5440155 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5440156 : term306 = term228.
Proof. exact (EQ_MP (@lem5440155) (@lem940073)). Qed.
Lemma lem5440157 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5440158 : term304 = term227.
Proof. exact (MK_COMB (@lem5440157) (@lem5440156)). Qed.
Lemma lem5440159 : term303 = term227.
Proof. exact (TRANS (@lem5440154) (@lem5440158)). Qed.
Lemma lem5440160 : term744 = term744.
Proof. exact (eq_refl term744). Qed.
Lemma lem5440161 : term746 = term711.
Proof. exact (MK_COMB (@lem5440160) (@lem5440159)). Qed.
Lemma lem5440163 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5440164 : term711 = term214.
Proof. exact (@lem5440163 term228). Qed.
Lemma lem5440165 : term746 = term214.
Proof. exact (TRANS (@lem5440161) (@lem5440164)). Qed.
Lemma lem5440166 : term214 = term746.
Proof. exact (SYM (@lem5440165)). Qed.
Lemma lem5440167 : term745 = term746.
Proof. exact (TRANS (@lem5440151) (@lem5440166)). Qed.
Lemma lem5440168 : term735 = term291.
Proof. exact (@lem5440118 (@lem5440167)). Qed.
Lemma lem5440169 : term734 = term291.
Proof. exact (TRANS (@lem5440084) (@lem5440168)). Qed.
Lemma lem5440171 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5440172 : term291 = term214.
Proof. exact (@lem5440171 term214). Qed.
Lemma lem5440173 : term734 = term214.
Proof. exact (TRANS (@lem5440169) (@lem5440172)). Qed.
Lemma lem5440174 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5440175 : term747 = term744.
Proof. exact (MK_COMB (@lem5440174) (@lem5440173)). Qed.
Lemma lem5440176 (_70504 : int) : (real_of_int _70504) = (real_of_int _70504).
Proof. exact (eq_refl (real_of_int _70504)). Qed.
Lemma lem5440177 (_70504 : int) : (term731 _70504) = (term748 _70504).
Proof. exact (MK_COMB (@lem5440175) (@lem5440176 _70504)). Qed.
Lemma lem5440178 (_70504 : int) : (term730 _70504) = (term748 _70504).
Proof. exact (TRANS (@lem5440075 _70504) (@lem5440177 _70504)). Qed.
Lemma lem5440179 (_70504 : int) : (term748 _70504) = term214.
Proof. exact (@lem1982719 (real_of_int _70504)). Qed.
Lemma lem5440180 (_70504 : int) : (term730 _70504) = term214.
Proof. exact (TRANS (@lem5440178 _70504) (@lem5440179 _70504)). Qed.
Lemma lem5440181 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5440182 (_70504 : int) : (term749 _70504) = term750.
Proof. exact (MK_COMB (@lem5440181) (@lem5440180 _70504)). Qed.
Lemma lem5440183 (_70508 : int) : (term751 _70508) = (term752 _70508).
Proof. exact (@lem1982763 (real_of_int _70508) (term336 _70508) term294). Qed.
Lemma lem5440184 (_70508 : int) : (term753 _70508) = (term731 _70508).
Proof. exact (@lem1982715 term294 (real_of_int _70508)). Qed.
Lemma lem5440186 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5440187 : term227 = term320.
Proof. exact (@lem5440186 term228). Qed.
Lemma lem5440189 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5440190 : term294 = term295.
Proof. exact (@lem5440189 term228). Qed.
Lemma lem5440191 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5440192 : term732 = term733.
Proof. exact (MK_COMB (@lem5440191) (@lem5440190)). Qed.
Lemma lem5440193 : term734 = term735.
Proof. exact (MK_COMB (@lem5440192) (@lem5440187)). Qed.
Lemma lem5440194 : term736.
Proof. exact (@lem1981473 term294 term227 term227 term227 term214 term227). Qed.
Lemma lem5440196 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440197 : term700 = term706.
Proof. exact (@lem5440196 (NUMERAL 0) term228). Qed.
Lemma lem5440198 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440199 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440200 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440199 h1) (fun h1 : term706 = True => @lem5440198)). Qed.
Lemma lem5440201 : term706 = True.
Proof. exact (EQ_MP (@lem5440200) (@lem5440198)). Qed.
Lemma lem5440202 : term700 = True.
Proof. exact (TRANS (@lem5440197) (@lem5440201)). Qed.
Lemma lem5440203 : True = term700.
Proof. exact (SYM (@lem5440202)). Qed.
Lemma lem5440204 : term700.
Proof. exact (EQ_MP (@lem5440203) (@lem0)). Qed.
Lemma lem5440205 : term737.
Proof. exact (@lem5440194 (@lem5440204)). Qed.
Lemma lem5440207 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440208 : term700 = term706.
Proof. exact (@lem5440207 (NUMERAL 0) term228). Qed.
Lemma lem5440209 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440210 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440211 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440210 h1) (fun h1 : term706 = True => @lem5440209)). Qed.
Lemma lem5440212 : term706 = True.
Proof. exact (EQ_MP (@lem5440211) (@lem5440209)). Qed.
Lemma lem5440213 : term700 = True.
Proof. exact (TRANS (@lem5440208) (@lem5440212)). Qed.
Lemma lem5440214 : True = term700.
Proof. exact (SYM (@lem5440213)). Qed.
Lemma lem5440215 : term700.
Proof. exact (EQ_MP (@lem5440214) (@lem0)). Qed.
Lemma lem5440216 : term738.
Proof. exact (@lem5440205 (@lem5440215)). Qed.
Lemma lem5440218 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440219 : term700 = term706.
Proof. exact (@lem5440218 (NUMERAL 0) term228). Qed.
Lemma lem5440220 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440221 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440222 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440221 h1) (fun h1 : term706 = True => @lem5440220)). Qed.
Lemma lem5440223 : term706 = True.
Proof. exact (EQ_MP (@lem5440222) (@lem5440220)). Qed.
Lemma lem5440224 : term700 = True.
Proof. exact (TRANS (@lem5440219) (@lem5440223)). Qed.
Lemma lem5440225 : True = term700.
Proof. exact (SYM (@lem5440224)). Qed.
Lemma lem5440226 : term700.
Proof. exact (EQ_MP (@lem5440225) (@lem0)). Qed.
Lemma lem5440227 : term739.
Proof. exact (@lem5440216 (@lem5440226)). Qed.
Lemma lem5440229 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5440230 : term303 = term304.
Proof. exact (@lem5440229 term228 term228). Qed.
Lemma lem5440231 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5440232 : term306 = term228.
Proof. exact (EQ_MP (@lem5440231) (@lem940073)). Qed.
Lemma lem5440233 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5440234 : term304 = term227.
Proof. exact (MK_COMB (@lem5440233) (@lem5440232)). Qed.
Lemma lem5440235 : term303 = term227.
Proof. exact (TRANS (@lem5440230) (@lem5440234)). Qed.
Lemma lem5440237 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5440238 : term321 = term326.
Proof. exact (@lem5440237 term228 term228). Qed.
Lemma lem5440239 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5440240 : term306 = term228.
Proof. exact (EQ_MP (@lem5440239) (@lem940073)). Qed.
Lemma lem5440241 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5440242 : term304 = term227.
Proof. exact (MK_COMB (@lem5440241) (@lem5440240)). Qed.
Lemma lem5440243 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5440244 : term326 = term294.
Proof. exact (MK_COMB (@lem5440243) (@lem5440242)). Qed.
Lemma lem5440245 : term321 = term294.
Proof. exact (TRANS (@lem5440238) (@lem5440244)). Qed.
Lemma lem5440246 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5440247 : term740 = term732.
Proof. exact (MK_COMB (@lem5440246) (@lem5440245)). Qed.
Lemma lem5440248 : term741 = term734.
Proof. exact (MK_COMB (@lem5440247) (@lem5440235)). Qed.
Lemma lem5440250 (m : nat) : (term742 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5440251 : term734 = term214.
Proof. exact (@lem5440250 term228). Qed.
Lemma lem5440252 : term741 = term214.
Proof. exact (TRANS (@lem5440248) (@lem5440251)). Qed.
Lemma lem5440253 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5440254 : term743 = term744.
Proof. exact (MK_COMB (@lem5440253) (@lem5440252)). Qed.
Lemma lem5440255 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem5440256 : term745 = term711.
Proof. exact (MK_COMB (@lem5440254) (@lem5440255)). Qed.
Lemma lem5440258 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5440259 : term711 = term214.
Proof. exact (@lem5440258 term228). Qed.
Lemma lem5440260 : term745 = term214.
Proof. exact (TRANS (@lem5440256) (@lem5440259)). Qed.
Lemma lem5440262 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5440263 : term303 = term304.
Proof. exact (@lem5440262 term228 term228). Qed.
Lemma lem5440264 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5440265 : term306 = term228.
Proof. exact (EQ_MP (@lem5440264) (@lem940073)). Qed.
Lemma lem5440266 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5440267 : term304 = term227.
Proof. exact (MK_COMB (@lem5440266) (@lem5440265)). Qed.
Lemma lem5440268 : term303 = term227.
Proof. exact (TRANS (@lem5440263) (@lem5440267)). Qed.
Lemma lem5440269 : term744 = term744.
Proof. exact (eq_refl term744). Qed.
Lemma lem5440270 : term746 = term711.
Proof. exact (MK_COMB (@lem5440269) (@lem5440268)). Qed.
Lemma lem5440272 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5440273 : term711 = term214.
Proof. exact (@lem5440272 term228). Qed.
Lemma lem5440274 : term746 = term214.
Proof. exact (TRANS (@lem5440270) (@lem5440273)). Qed.
Lemma lem5440275 : term214 = term746.
Proof. exact (SYM (@lem5440274)). Qed.
Lemma lem5440276 : term745 = term746.
Proof. exact (TRANS (@lem5440260) (@lem5440275)). Qed.
Lemma lem5440277 : term735 = term291.
Proof. exact (@lem5440227 (@lem5440276)). Qed.
Lemma lem5440278 : term734 = term291.
Proof. exact (TRANS (@lem5440193) (@lem5440277)). Qed.
Lemma lem5440280 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5440281 : term291 = term214.
Proof. exact (@lem5440280 term214). Qed.
Lemma lem5440282 : term734 = term214.
Proof. exact (TRANS (@lem5440278) (@lem5440281)). Qed.
Lemma lem5440283 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5440284 : term747 = term744.
Proof. exact (MK_COMB (@lem5440283) (@lem5440282)). Qed.
Lemma lem5440285 (_70508 : int) : (real_of_int _70508) = (real_of_int _70508).
Proof. exact (eq_refl (real_of_int _70508)). Qed.
Lemma lem5440286 (_70508 : int) : (term731 _70508) = (term748 _70508).
Proof. exact (MK_COMB (@lem5440284) (@lem5440285 _70508)). Qed.
Lemma lem5440287 (_70508 : int) : (term753 _70508) = (term748 _70508).
Proof. exact (TRANS (@lem5440184 _70508) (@lem5440286 _70508)). Qed.
Lemma lem5440288 (_70508 : int) : (term748 _70508) = term214.
Proof. exact (@lem1982719 (real_of_int _70508)). Qed.
Lemma lem5440289 (_70508 : int) : (term753 _70508) = term214.
Proof. exact (TRANS (@lem5440287 _70508) (@lem5440288 _70508)). Qed.
Lemma lem5440290 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5440291 (_70508 : int) : (term754 _70508) = term750.
Proof. exact (MK_COMB (@lem5440290) (@lem5440289 _70508)). Qed.
Lemma lem5440292 : term294 = term294.
Proof. exact (eq_refl term294). Qed.
Lemma lem5440293 (_70508 : int) : (term752 _70508) = term755.
Proof. exact (MK_COMB (@lem5440291 _70508) (@lem5440292)). Qed.
Lemma lem5440294 (_70508 : int) : (term751 _70508) = term755.
Proof. exact (TRANS (@lem5440183 _70508) (@lem5440293 _70508)). Qed.
Lemma lem5440295 : term755 = term294.
Proof. exact (@lem1982721 term294). Qed.
Lemma lem5440296 (_70508 : int) : (term751 _70508) = term294.
Proof. exact (TRANS (@lem5440294 _70508) (@lem5440295)). Qed.
Lemma lem5440297 (_70504 : int) (_70508 : int) : (term729 _70504 _70508) = term755.
Proof. exact (MK_COMB (@lem5440182 _70504) (@lem5440296 _70508)). Qed.
Lemma lem5440298 (_70504 : int) (_70508 : int) : (term728 _70504 _70508) = term755.
Proof. exact (TRANS (@lem5440074 _70504 _70508) (@lem5440297 _70504 _70508)). Qed.
Lemma lem5440299 : term755 = term294.
Proof. exact (@lem1982721 term294). Qed.
Lemma lem5440300 (_70504 : int) (_70508 : int) : (term728 _70504 _70508) = term294.
Proof. exact (TRANS (@lem5440298 _70504 _70508) (@lem5440299)). Qed.
Lemma lem5440301 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5440302 (_70504 : int) (_70508 : int) : (term756 _70504 _70508) = term757.
Proof. exact (MK_COMB (@lem5440301) (@lem5440300 _70504 _70508)). Qed.
Lemma lem5440303 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5440304 (_70504 : int) (_70508 : int) : (term727 _70504 _70508) = term758.
Proof. exact (MK_COMB (@lem5440302 _70504 _70508) (@lem5440303)). Qed.
Lemma lem5440305 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term544 _70504 _70506 _70505 _70507 _70508) : term758.
Proof. exact (EQ_MP (@lem5440304 _70504 _70508) (@lem5440073 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440307 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5440308 : term758 = term759.
Proof. exact (@lem5440307 term214 term294). Qed.
Lemma lem5440310 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5440311 : term294 = term295.
Proof. exact (@lem5440310 term228). Qed.
Lemma lem5440313 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5440314 : term214 = term291.
Proof. exact (@lem5440313 (NUMERAL 0)). Qed.
Lemma lem5440315 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5440316 : term216 = term760.
Proof. exact (MK_COMB (@lem5440315) (@lem5440314)). Qed.
Lemma lem5440317 : term759 = term761.
Proof. exact (MK_COMB (@lem5440316) (@lem5440311)). Qed.
Lemma lem5440318 : term762.
Proof. exact (@lem1980026 term214 term227 term294 term227). Qed.
Lemma lem5440320 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440321 : term700 = term706.
Proof. exact (@lem5440320 (NUMERAL 0) term228). Qed.
Lemma lem5440322 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440323 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440324 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440323 h1) (fun h1 : term706 = True => @lem5440322)). Qed.
Lemma lem5440325 : term706 = True.
Proof. exact (EQ_MP (@lem5440324) (@lem5440322)). Qed.
Lemma lem5440326 : term700 = True.
Proof. exact (TRANS (@lem5440321) (@lem5440325)). Qed.
Lemma lem5440327 : True = term700.
Proof. exact (SYM (@lem5440326)). Qed.
Lemma lem5440328 : term700.
Proof. exact (EQ_MP (@lem5440327) (@lem0)). Qed.
Lemma lem5440329 : term763.
Proof. exact (@lem5440318 (@lem5440328)). Qed.
Lemma lem5440331 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440332 : term700 = term706.
Proof. exact (@lem5440331 (NUMERAL 0) term228). Qed.
Lemma lem5440333 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440334 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440335 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440334 h1) (fun h1 : term706 = True => @lem5440333)). Qed.
Lemma lem5440336 : term706 = True.
Proof. exact (EQ_MP (@lem5440335) (@lem5440333)). Qed.
Lemma lem5440337 : term700 = True.
Proof. exact (TRANS (@lem5440332) (@lem5440336)). Qed.
Lemma lem5440338 : True = term700.
Proof. exact (SYM (@lem5440337)). Qed.
Lemma lem5440339 : term700.
Proof. exact (EQ_MP (@lem5440338) (@lem0)). Qed.
Lemma lem5440340 : term761 = term764.
Proof. exact (@lem5440329 (@lem5440339)). Qed.
Lemma lem5440342 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5440343 : term321 = term326.
Proof. exact (@lem5440342 term228 term228). Qed.
Lemma lem5440344 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5440345 : term306 = term228.
Proof. exact (EQ_MP (@lem5440344) (@lem940073)). Qed.
Lemma lem5440346 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5440347 : term304 = term227.
Proof. exact (MK_COMB (@lem5440346) (@lem5440345)). Qed.
Lemma lem5440348 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5440349 : term326 = term294.
Proof. exact (MK_COMB (@lem5440348) (@lem5440347)). Qed.
Lemma lem5440350 : term321 = term294.
Proof. exact (TRANS (@lem5440343) (@lem5440349)). Qed.
Lemma lem5440352 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5440353 : term711 = term214.
Proof. exact (@lem5440352 term228). Qed.
Lemma lem5440354 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5440355 : term765 = term216.
Proof. exact (MK_COMB (@lem5440354) (@lem5440353)). Qed.
Lemma lem5440356 : term764 = term759.
Proof. exact (MK_COMB (@lem5440355) (@lem5440350)). Qed.
Lemma lem5440358 (m : nat) (n : nat) : (term766 m n) = (term767 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5440359 : term759 = term768.
Proof. exact (@lem5440358 (NUMERAL 0) term228). Qed.
Lemma lem5440360 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440361 (h1 : term707 = (BIT1 0)) : (term228 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5440362 : (term707 = (BIT1 0)) = ((term228 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440361 h1) (fun h1 : (term228 = (NUMERAL 0)) = False => @lem5440360)). Qed.
Lemma lem5440363 : (term228 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5440362) (@lem5440360)). Qed.
Lemma lem5440364 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5440365 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5440366 : term769 = (and True).
Proof. exact (MK_COMB (@lem5440365) (@lem5440364)). Qed.
Lemma lem5440367 : term768 = (True /\ False).
Proof. exact (MK_COMB (@lem5440366) (@lem5440363)). Qed.
Lemma lem5440369 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5440370 : term768 = False.
Proof. exact (TRANS (@lem5440367) (@lem5440369)). Qed.
Lemma lem5440371 : term759 = False.
Proof. exact (TRANS (@lem5440359) (@lem5440370)). Qed.
Lemma lem5440372 : term764 = False.
Proof. exact (TRANS (@lem5440356) (@lem5440371)). Qed.
Lemma lem5440373 : term761 = False.
Proof. exact (TRANS (@lem5440340) (@lem5440372)). Qed.
Lemma lem5440374 : term759 = False.
Proof. exact (TRANS (@lem5440317) (@lem5440373)). Qed.
Lemma lem5440375 : term758 = False.
Proof. exact (TRANS (@lem5440308) (@lem5440374)). Qed.
Lemma lem5440376 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term544 _70504 _70506 _70505 _70507 _70508) : False.
Proof. exact (EQ_MP (@lem5440375) (@lem5440305 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440377 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term552 _70504 _70506 _70505 _70507 _70508) : term552 _70504 _70506 _70505 _70507 _70508.
Proof. exact (h1). Qed.
Lemma lem5440378 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term552 _70504 _70506 _70505 _70507 _70508) : term550 _70504 _70506 _70505 _70507 _70508.
Proof. exact (proj2 (@lem5440377 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440380 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term552 _70504 _70506 _70505 _70507 _70508) : term549 _70504 _70506 _70505 _70507 _70508.
Proof. exact (proj2 (@lem5440378 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440382 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term552 _70504 _70506 _70505 _70507 _70508) : term548 _70504 _70506 _70505 _70507 _70508.
Proof. exact (proj2 (@lem5440380 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440384 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term552 _70504 _70506 _70505 _70507 _70508) : term547 _70504 _70506 _70505 _70507 _70508.
Proof. exact (proj2 (@lem5440382 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440386 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term552 _70504 _70506 _70505 _70507 _70508) : term546 _70504 _70506 _70505 _70507 _70508.
Proof. exact (proj2 (@lem5440384 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440388 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term552 _70504 _70506 _70505 _70507 _70508) : term536 _70504 _70506 _70505 _70507 _70508.
Proof. exact (proj2 (@lem5440386 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440389 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term552 _70504 _70506 _70505 _70507 _70508) : term338 _70505 _70508.
Proof. exact (proj1 (@lem5440386 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440390 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term552 _70504 _70506 _70505 _70507 _70508) : term535 _70505 _70507 _70508.
Proof. exact (proj2 (@lem5440388 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440395 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term552 _70504 _70506 _70505 _70507 _70508) : term368 _70505 _70508.
Proof. exact (proj1 (@lem5440390 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440397 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5440398 : term699 = term700.
Proof. exact (@lem5440397 term214 term227). Qed.
Lemma lem5440400 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5440401 : term227 = term320.
Proof. exact (@lem5440400 term228). Qed.
Lemma lem5440403 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5440404 : term214 = term291.
Proof. exact (@lem5440403 (NUMERAL 0)). Qed.
Lemma lem5440405 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5440406 : term701 = term702.
Proof. exact (MK_COMB (@lem5440405) (@lem5440404)). Qed.
Lemma lem5440407 : term700 = term703.
Proof. exact (MK_COMB (@lem5440406) (@lem5440401)). Qed.
Lemma lem5440408 : term704.
Proof. exact (@lem1980255 term214 term227 term227 term227). Qed.
Lemma lem5440410 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440411 : term700 = term706.
Proof. exact (@lem5440410 (NUMERAL 0) term228). Qed.
Lemma lem5440412 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440413 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440414 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440413 h1) (fun h1 : term706 = True => @lem5440412)). Qed.
Lemma lem5440415 : term706 = True.
Proof. exact (EQ_MP (@lem5440414) (@lem5440412)). Qed.
Lemma lem5440416 : term700 = True.
Proof. exact (TRANS (@lem5440411) (@lem5440415)). Qed.
Lemma lem5440417 : True = term700.
Proof. exact (SYM (@lem5440416)). Qed.
Lemma lem5440418 : term700.
Proof. exact (EQ_MP (@lem5440417) (@lem0)). Qed.
Lemma lem5440419 : term708.
Proof. exact (@lem5440408 (@lem5440418)). Qed.
Lemma lem5440421 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440422 : term700 = term706.
Proof. exact (@lem5440421 (NUMERAL 0) term228). Qed.
Lemma lem5440423 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440424 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440425 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440424 h1) (fun h1 : term706 = True => @lem5440423)). Qed.
Lemma lem5440426 : term706 = True.
Proof. exact (EQ_MP (@lem5440425) (@lem5440423)). Qed.
Lemma lem5440427 : term700 = True.
Proof. exact (TRANS (@lem5440422) (@lem5440426)). Qed.
Lemma lem5440428 : True = term700.
Proof. exact (SYM (@lem5440427)). Qed.
Lemma lem5440429 : term700.
Proof. exact (EQ_MP (@lem5440428) (@lem0)). Qed.
Lemma lem5440430 : term703 = term709.
Proof. exact (@lem5440419 (@lem5440429)). Qed.
Lemma lem5440432 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5440433 : term303 = term304.
Proof. exact (@lem5440432 term228 term228). Qed.
Lemma lem5440434 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5440435 : term306 = term228.
Proof. exact (EQ_MP (@lem5440434) (@lem940073)). Qed.
Lemma lem5440436 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5440437 : term304 = term227.
Proof. exact (MK_COMB (@lem5440436) (@lem5440435)). Qed.
Lemma lem5440438 : term303 = term227.
Proof. exact (TRANS (@lem5440433) (@lem5440437)). Qed.
Lemma lem5440440 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5440441 : term711 = term214.
Proof. exact (@lem5440440 term228). Qed.
Lemma lem5440442 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5440443 : term712 = term701.
Proof. exact (MK_COMB (@lem5440442) (@lem5440441)). Qed.
Lemma lem5440444 : term709 = term700.
Proof. exact (MK_COMB (@lem5440443) (@lem5440438)). Qed.
Lemma lem5440446 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440447 : term700 = term706.
Proof. exact (@lem5440446 (NUMERAL 0) term228). Qed.
Lemma lem5440448 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440449 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440450 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440449 h1) (fun h1 : term706 = True => @lem5440448)). Qed.
Lemma lem5440451 : term706 = True.
Proof. exact (EQ_MP (@lem5440450) (@lem5440448)). Qed.
Lemma lem5440452 : term700 = True.
Proof. exact (TRANS (@lem5440447) (@lem5440451)). Qed.
Lemma lem5440453 : term709 = True.
Proof. exact (TRANS (@lem5440444) (@lem5440452)). Qed.
Lemma lem5440454 : term703 = True.
Proof. exact (TRANS (@lem5440430) (@lem5440453)). Qed.
Lemma lem5440455 : term700 = True.
Proof. exact (TRANS (@lem5440407) (@lem5440454)). Qed.
Lemma lem5440456 : term699 = True.
Proof. exact (TRANS (@lem5440398) (@lem5440455)). Qed.
Lemma lem5440457 : True = term699.
Proof. exact (SYM (@lem5440456)). Qed.
Lemma lem5440458 : term699.
Proof. exact (EQ_MP (@lem5440457) (@lem0)). Qed.
Lemma lem5440459 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term552 _70504 _70506 _70505 _70507 _70508) : term770 _70505 _70508.
Proof. exact (conj (@lem5440458) (@lem5440395 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440461 (x : real) (y : real) : term714 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5440462 (_70505 : int) (_70508 : int) : term771 _70505 _70508.
Proof. exact (@lem5440461 term227 (term362 _70505 _70508)). Qed.
Lemma lem5440463 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term552 _70504 _70506 _70505 _70507 _70508) : term772 _70505 _70508.
Proof. exact (@lem5440462 _70505 _70508 (@lem5440459 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440464 (_70505 : int) (_70508 : int) : (term773 _70505 _70508) = (term362 _70505 _70508).
Proof. exact (@lem1982733 (term362 _70505 _70508)). Qed.
Lemma lem5440465 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5440466 (_70505 : int) (_70508 : int) : (term774 _70505 _70508) = (term367 _70505 _70508).
Proof. exact (MK_COMB (@lem5440465) (@lem5440464 _70505 _70508)). Qed.
Lemma lem5440467 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5440468 (_70505 : int) (_70508 : int) : (term772 _70505 _70508) = (term368 _70505 _70508).
Proof. exact (MK_COMB (@lem5440466 _70505 _70508) (@lem5440467)). Qed.
Lemma lem5440469 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term552 _70504 _70506 _70505 _70507 _70508) : term368 _70505 _70508.
Proof. exact (EQ_MP (@lem5440468 _70505 _70508) (@lem5440463 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440471 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5440472 : term699 = term700.
Proof. exact (@lem5440471 term214 term227). Qed.
Lemma lem5440474 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5440475 : term227 = term320.
Proof. exact (@lem5440474 term228). Qed.
Lemma lem5440477 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5440478 : term214 = term291.
Proof. exact (@lem5440477 (NUMERAL 0)). Qed.
Lemma lem5440479 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5440480 : term701 = term702.
Proof. exact (MK_COMB (@lem5440479) (@lem5440478)). Qed.
Lemma lem5440481 : term700 = term703.
Proof. exact (MK_COMB (@lem5440480) (@lem5440475)). Qed.
Lemma lem5440482 : term704.
Proof. exact (@lem1980255 term214 term227 term227 term227). Qed.
Lemma lem5440484 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440485 : term700 = term706.
Proof. exact (@lem5440484 (NUMERAL 0) term228). Qed.
Lemma lem5440486 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440487 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440488 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440487 h1) (fun h1 : term706 = True => @lem5440486)). Qed.
Lemma lem5440489 : term706 = True.
Proof. exact (EQ_MP (@lem5440488) (@lem5440486)). Qed.
Lemma lem5440490 : term700 = True.
Proof. exact (TRANS (@lem5440485) (@lem5440489)). Qed.
Lemma lem5440491 : True = term700.
Proof. exact (SYM (@lem5440490)). Qed.
Lemma lem5440492 : term700.
Proof. exact (EQ_MP (@lem5440491) (@lem0)). Qed.
Lemma lem5440493 : term708.
Proof. exact (@lem5440482 (@lem5440492)). Qed.
Lemma lem5440495 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440496 : term700 = term706.
Proof. exact (@lem5440495 (NUMERAL 0) term228). Qed.
Lemma lem5440497 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440498 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440499 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440498 h1) (fun h1 : term706 = True => @lem5440497)). Qed.
Lemma lem5440500 : term706 = True.
Proof. exact (EQ_MP (@lem5440499) (@lem5440497)). Qed.
Lemma lem5440501 : term700 = True.
Proof. exact (TRANS (@lem5440496) (@lem5440500)). Qed.
Lemma lem5440502 : True = term700.
Proof. exact (SYM (@lem5440501)). Qed.
Lemma lem5440503 : term700.
Proof. exact (EQ_MP (@lem5440502) (@lem0)). Qed.
Lemma lem5440504 : term703 = term709.
Proof. exact (@lem5440493 (@lem5440503)). Qed.
Lemma lem5440506 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5440507 : term303 = term304.
Proof. exact (@lem5440506 term228 term228). Qed.
Lemma lem5440508 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5440509 : term306 = term228.
Proof. exact (EQ_MP (@lem5440508) (@lem940073)). Qed.
Lemma lem5440510 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5440511 : term304 = term227.
Proof. exact (MK_COMB (@lem5440510) (@lem5440509)). Qed.
Lemma lem5440512 : term303 = term227.
Proof. exact (TRANS (@lem5440507) (@lem5440511)). Qed.
Lemma lem5440514 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5440515 : term711 = term214.
Proof. exact (@lem5440514 term228). Qed.
Lemma lem5440516 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5440517 : term712 = term701.
Proof. exact (MK_COMB (@lem5440516) (@lem5440515)). Qed.
Lemma lem5440518 : term709 = term700.
Proof. exact (MK_COMB (@lem5440517) (@lem5440512)). Qed.
Lemma lem5440520 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440521 : term700 = term706.
Proof. exact (@lem5440520 (NUMERAL 0) term228). Qed.
Lemma lem5440522 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440523 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440524 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440523 h1) (fun h1 : term706 = True => @lem5440522)). Qed.
Lemma lem5440525 : term706 = True.
Proof. exact (EQ_MP (@lem5440524) (@lem5440522)). Qed.
Lemma lem5440526 : term700 = True.
Proof. exact (TRANS (@lem5440521) (@lem5440525)). Qed.
Lemma lem5440527 : term709 = True.
Proof. exact (TRANS (@lem5440518) (@lem5440526)). Qed.
Lemma lem5440528 : term703 = True.
Proof. exact (TRANS (@lem5440504) (@lem5440527)). Qed.
Lemma lem5440529 : term700 = True.
Proof. exact (TRANS (@lem5440481) (@lem5440528)). Qed.
Lemma lem5440530 : term699 = True.
Proof. exact (TRANS (@lem5440472) (@lem5440529)). Qed.
Lemma lem5440531 : True = term699.
Proof. exact (SYM (@lem5440530)). Qed.
Lemma lem5440532 : term699.
Proof. exact (EQ_MP (@lem5440531) (@lem0)). Qed.
Lemma lem5440533 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term552 _70504 _70506 _70505 _70507 _70508) : term775 _70505 _70508.
Proof. exact (conj (@lem5440532) (@lem5440389 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440535 (x : real) (y : real) : term714 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5440536 (_70505 : int) (_70508 : int) : term776 _70505 _70508.
Proof. exact (@lem5440535 term227 (term335 _70505 _70508)). Qed.
Lemma lem5440537 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term552 _70504 _70506 _70505 _70507 _70508) : term777 _70505 _70508.
Proof. exact (@lem5440536 _70505 _70508 (@lem5440533 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440538 (_70505 : int) (_70508 : int) : (term778 _70505 _70508) = (term335 _70505 _70508).
Proof. exact (@lem1982733 (term335 _70505 _70508)). Qed.
Lemma lem5440539 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5440540 (_70505 : int) (_70508 : int) : (term779 _70505 _70508) = (term337 _70505 _70508).
Proof. exact (MK_COMB (@lem5440539) (@lem5440538 _70505 _70508)). Qed.
Lemma lem5440541 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5440542 (_70505 : int) (_70508 : int) : (term777 _70505 _70508) = (term338 _70505 _70508).
Proof. exact (MK_COMB (@lem5440540 _70505 _70508) (@lem5440541)). Qed.
Lemma lem5440543 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term552 _70504 _70506 _70505 _70507 _70508) : term338 _70505 _70508.
Proof. exact (EQ_MP (@lem5440542 _70505 _70508) (@lem5440537 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440544 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term552 _70504 _70506 _70505 _70507 _70508) : term780 _70505 _70508.
Proof. exact (conj (@lem5440543 _70504 _70506 _70505 _70507 _70508 h1) (@lem5440469 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440546 (x : real) (y : real) : term725 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5440547 (_70505 : int) (_70508 : int) : term781 _70505 _70508.
Proof. exact (@lem5440546 (term335 _70505 _70508) (term362 _70505 _70508)). Qed.
Lemma lem5440548 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term552 _70504 _70506 _70505 _70507 _70508) : term782 _70505 _70508.
Proof. exact (@lem5440547 _70505 _70508 (@lem5440544 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440549 (_70505 : int) (_70508 : int) : (term783 _70505 _70508) = (term784 _70505 _70508).
Proof. exact (@lem1982753 (term336 _70505) (real_of_int _70505) (term785 _70508) (term336 _70508)). Qed.
Lemma lem5440550 (_70505 : int) : (term730 _70505) = (term731 _70505).
Proof. exact (@lem1982713 term294 (real_of_int _70505)). Qed.
Lemma lem5440552 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5440553 : term227 = term320.
Proof. exact (@lem5440552 term228). Qed.
Lemma lem5440555 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5440556 : term294 = term295.
Proof. exact (@lem5440555 term228). Qed.
Lemma lem5440557 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5440558 : term732 = term733.
Proof. exact (MK_COMB (@lem5440557) (@lem5440556)). Qed.
Lemma lem5440559 : term734 = term735.
Proof. exact (MK_COMB (@lem5440558) (@lem5440553)). Qed.
Lemma lem5440560 : term736.
Proof. exact (@lem1981473 term294 term227 term227 term227 term214 term227). Qed.
Lemma lem5440562 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440563 : term700 = term706.
Proof. exact (@lem5440562 (NUMERAL 0) term228). Qed.
Lemma lem5440564 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440565 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440566 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440565 h1) (fun h1 : term706 = True => @lem5440564)). Qed.
Lemma lem5440567 : term706 = True.
Proof. exact (EQ_MP (@lem5440566) (@lem5440564)). Qed.
Lemma lem5440568 : term700 = True.
Proof. exact (TRANS (@lem5440563) (@lem5440567)). Qed.
Lemma lem5440569 : True = term700.
Proof. exact (SYM (@lem5440568)). Qed.
Lemma lem5440570 : term700.
Proof. exact (EQ_MP (@lem5440569) (@lem0)). Qed.
Lemma lem5440571 : term737.
Proof. exact (@lem5440560 (@lem5440570)). Qed.
Lemma lem5440573 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440574 : term700 = term706.
Proof. exact (@lem5440573 (NUMERAL 0) term228). Qed.
Lemma lem5440575 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440576 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440577 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440576 h1) (fun h1 : term706 = True => @lem5440575)). Qed.
Lemma lem5440578 : term706 = True.
Proof. exact (EQ_MP (@lem5440577) (@lem5440575)). Qed.
Lemma lem5440579 : term700 = True.
Proof. exact (TRANS (@lem5440574) (@lem5440578)). Qed.
Lemma lem5440580 : True = term700.
Proof. exact (SYM (@lem5440579)). Qed.
Lemma lem5440581 : term700.
Proof. exact (EQ_MP (@lem5440580) (@lem0)). Qed.
Lemma lem5440582 : term738.
Proof. exact (@lem5440571 (@lem5440581)). Qed.
Lemma lem5440584 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440585 : term700 = term706.
Proof. exact (@lem5440584 (NUMERAL 0) term228). Qed.
Lemma lem5440586 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440587 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440588 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440587 h1) (fun h1 : term706 = True => @lem5440586)). Qed.
Lemma lem5440589 : term706 = True.
Proof. exact (EQ_MP (@lem5440588) (@lem5440586)). Qed.
Lemma lem5440590 : term700 = True.
Proof. exact (TRANS (@lem5440585) (@lem5440589)). Qed.
Lemma lem5440591 : True = term700.
Proof. exact (SYM (@lem5440590)). Qed.
Lemma lem5440592 : term700.
Proof. exact (EQ_MP (@lem5440591) (@lem0)). Qed.
Lemma lem5440593 : term739.
Proof. exact (@lem5440582 (@lem5440592)). Qed.
Lemma lem5440595 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5440596 : term303 = term304.
Proof. exact (@lem5440595 term228 term228). Qed.
Lemma lem5440597 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5440598 : term306 = term228.
Proof. exact (EQ_MP (@lem5440597) (@lem940073)). Qed.
Lemma lem5440599 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5440600 : term304 = term227.
Proof. exact (MK_COMB (@lem5440599) (@lem5440598)). Qed.
Lemma lem5440601 : term303 = term227.
Proof. exact (TRANS (@lem5440596) (@lem5440600)). Qed.
Lemma lem5440603 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5440604 : term321 = term326.
Proof. exact (@lem5440603 term228 term228). Qed.
Lemma lem5440605 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5440606 : term306 = term228.
Proof. exact (EQ_MP (@lem5440605) (@lem940073)). Qed.
Lemma lem5440607 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5440608 : term304 = term227.
Proof. exact (MK_COMB (@lem5440607) (@lem5440606)). Qed.
Lemma lem5440609 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5440610 : term326 = term294.
Proof. exact (MK_COMB (@lem5440609) (@lem5440608)). Qed.
Lemma lem5440611 : term321 = term294.
Proof. exact (TRANS (@lem5440604) (@lem5440610)). Qed.
Lemma lem5440612 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5440613 : term740 = term732.
Proof. exact (MK_COMB (@lem5440612) (@lem5440611)). Qed.
Lemma lem5440614 : term741 = term734.
Proof. exact (MK_COMB (@lem5440613) (@lem5440601)). Qed.
Lemma lem5440616 (m : nat) : (term742 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5440617 : term734 = term214.
Proof. exact (@lem5440616 term228). Qed.
Lemma lem5440618 : term741 = term214.
Proof. exact (TRANS (@lem5440614) (@lem5440617)). Qed.
Lemma lem5440619 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5440620 : term743 = term744.
Proof. exact (MK_COMB (@lem5440619) (@lem5440618)). Qed.
Lemma lem5440621 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem5440622 : term745 = term711.
Proof. exact (MK_COMB (@lem5440620) (@lem5440621)). Qed.
Lemma lem5440624 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5440625 : term711 = term214.
Proof. exact (@lem5440624 term228). Qed.
Lemma lem5440626 : term745 = term214.
Proof. exact (TRANS (@lem5440622) (@lem5440625)). Qed.
Lemma lem5440628 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5440629 : term303 = term304.
Proof. exact (@lem5440628 term228 term228). Qed.
Lemma lem5440630 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5440631 : term306 = term228.
Proof. exact (EQ_MP (@lem5440630) (@lem940073)). Qed.
Lemma lem5440632 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5440633 : term304 = term227.
Proof. exact (MK_COMB (@lem5440632) (@lem5440631)). Qed.
Lemma lem5440634 : term303 = term227.
Proof. exact (TRANS (@lem5440629) (@lem5440633)). Qed.
Lemma lem5440635 : term744 = term744.
Proof. exact (eq_refl term744). Qed.
Lemma lem5440636 : term746 = term711.
Proof. exact (MK_COMB (@lem5440635) (@lem5440634)). Qed.
Lemma lem5440638 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5440639 : term711 = term214.
Proof. exact (@lem5440638 term228). Qed.
Lemma lem5440640 : term746 = term214.
Proof. exact (TRANS (@lem5440636) (@lem5440639)). Qed.
Lemma lem5440641 : term214 = term746.
Proof. exact (SYM (@lem5440640)). Qed.
Lemma lem5440642 : term745 = term746.
Proof. exact (TRANS (@lem5440626) (@lem5440641)). Qed.
Lemma lem5440643 : term735 = term291.
Proof. exact (@lem5440593 (@lem5440642)). Qed.
Lemma lem5440644 : term734 = term291.
Proof. exact (TRANS (@lem5440559) (@lem5440643)). Qed.
Lemma lem5440646 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5440647 : term291 = term214.
Proof. exact (@lem5440646 term214). Qed.
Lemma lem5440648 : term734 = term214.
Proof. exact (TRANS (@lem5440644) (@lem5440647)). Qed.
Lemma lem5440649 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5440650 : term747 = term744.
Proof. exact (MK_COMB (@lem5440649) (@lem5440648)). Qed.
Lemma lem5440651 (_70505 : int) : (real_of_int _70505) = (real_of_int _70505).
Proof. exact (eq_refl (real_of_int _70505)). Qed.
Lemma lem5440652 (_70505 : int) : (term731 _70505) = (term748 _70505).
Proof. exact (MK_COMB (@lem5440650) (@lem5440651 _70505)). Qed.
Lemma lem5440653 (_70505 : int) : (term730 _70505) = (term748 _70505).
Proof. exact (TRANS (@lem5440550 _70505) (@lem5440652 _70505)). Qed.
Lemma lem5440654 (_70505 : int) : (term748 _70505) = term214.
Proof. exact (@lem1982719 (real_of_int _70505)). Qed.
Lemma lem5440655 (_70505 : int) : (term730 _70505) = term214.
Proof. exact (TRANS (@lem5440653 _70505) (@lem5440654 _70505)). Qed.
Lemma lem5440656 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5440657 (_70505 : int) : (term749 _70505) = term750.
Proof. exact (MK_COMB (@lem5440656) (@lem5440655 _70505)). Qed.
Lemma lem5440658 (_70508 : int) : (term786 _70508) = (term752 _70508).
Proof. exact (@lem1982759 (real_of_int _70508) (term336 _70508) term294). Qed.
Lemma lem5440659 (_70508 : int) : (term753 _70508) = (term731 _70508).
Proof. exact (@lem1982715 term294 (real_of_int _70508)). Qed.
Lemma lem5440661 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5440662 : term227 = term320.
Proof. exact (@lem5440661 term228). Qed.
Lemma lem5440664 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5440665 : term294 = term295.
Proof. exact (@lem5440664 term228). Qed.
Lemma lem5440666 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5440667 : term732 = term733.
Proof. exact (MK_COMB (@lem5440666) (@lem5440665)). Qed.
Lemma lem5440668 : term734 = term735.
Proof. exact (MK_COMB (@lem5440667) (@lem5440662)). Qed.
Lemma lem5440669 : term736.
Proof. exact (@lem1981473 term294 term227 term227 term227 term214 term227). Qed.
Lemma lem5440671 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440672 : term700 = term706.
Proof. exact (@lem5440671 (NUMERAL 0) term228). Qed.
Lemma lem5440673 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440674 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440675 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440674 h1) (fun h1 : term706 = True => @lem5440673)). Qed.
Lemma lem5440676 : term706 = True.
Proof. exact (EQ_MP (@lem5440675) (@lem5440673)). Qed.
Lemma lem5440677 : term700 = True.
Proof. exact (TRANS (@lem5440672) (@lem5440676)). Qed.
Lemma lem5440678 : True = term700.
Proof. exact (SYM (@lem5440677)). Qed.
Lemma lem5440679 : term700.
Proof. exact (EQ_MP (@lem5440678) (@lem0)). Qed.
Lemma lem5440680 : term737.
Proof. exact (@lem5440669 (@lem5440679)). Qed.
Lemma lem5440682 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440683 : term700 = term706.
Proof. exact (@lem5440682 (NUMERAL 0) term228). Qed.
Lemma lem5440684 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440685 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440686 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440685 h1) (fun h1 : term706 = True => @lem5440684)). Qed.
Lemma lem5440687 : term706 = True.
Proof. exact (EQ_MP (@lem5440686) (@lem5440684)). Qed.
Lemma lem5440688 : term700 = True.
Proof. exact (TRANS (@lem5440683) (@lem5440687)). Qed.
Lemma lem5440689 : True = term700.
Proof. exact (SYM (@lem5440688)). Qed.
Lemma lem5440690 : term700.
Proof. exact (EQ_MP (@lem5440689) (@lem0)). Qed.
Lemma lem5440691 : term738.
Proof. exact (@lem5440680 (@lem5440690)). Qed.
Lemma lem5440693 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440694 : term700 = term706.
Proof. exact (@lem5440693 (NUMERAL 0) term228). Qed.
Lemma lem5440695 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440696 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440697 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440696 h1) (fun h1 : term706 = True => @lem5440695)). Qed.
Lemma lem5440698 : term706 = True.
Proof. exact (EQ_MP (@lem5440697) (@lem5440695)). Qed.
Lemma lem5440699 : term700 = True.
Proof. exact (TRANS (@lem5440694) (@lem5440698)). Qed.
Lemma lem5440700 : True = term700.
Proof. exact (SYM (@lem5440699)). Qed.
Lemma lem5440701 : term700.
Proof. exact (EQ_MP (@lem5440700) (@lem0)). Qed.
Lemma lem5440702 : term739.
Proof. exact (@lem5440691 (@lem5440701)). Qed.
Lemma lem5440704 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5440705 : term303 = term304.
Proof. exact (@lem5440704 term228 term228). Qed.
Lemma lem5440706 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5440707 : term306 = term228.
Proof. exact (EQ_MP (@lem5440706) (@lem940073)). Qed.
Lemma lem5440708 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5440709 : term304 = term227.
Proof. exact (MK_COMB (@lem5440708) (@lem5440707)). Qed.
Lemma lem5440710 : term303 = term227.
Proof. exact (TRANS (@lem5440705) (@lem5440709)). Qed.
Lemma lem5440712 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5440713 : term321 = term326.
Proof. exact (@lem5440712 term228 term228). Qed.
Lemma lem5440714 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5440715 : term306 = term228.
Proof. exact (EQ_MP (@lem5440714) (@lem940073)). Qed.
Lemma lem5440716 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5440717 : term304 = term227.
Proof. exact (MK_COMB (@lem5440716) (@lem5440715)). Qed.
Lemma lem5440718 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5440719 : term326 = term294.
Proof. exact (MK_COMB (@lem5440718) (@lem5440717)). Qed.
Lemma lem5440720 : term321 = term294.
Proof. exact (TRANS (@lem5440713) (@lem5440719)). Qed.
Lemma lem5440721 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5440722 : term740 = term732.
Proof. exact (MK_COMB (@lem5440721) (@lem5440720)). Qed.
Lemma lem5440723 : term741 = term734.
Proof. exact (MK_COMB (@lem5440722) (@lem5440710)). Qed.
Lemma lem5440725 (m : nat) : (term742 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5440726 : term734 = term214.
Proof. exact (@lem5440725 term228). Qed.
Lemma lem5440727 : term741 = term214.
Proof. exact (TRANS (@lem5440723) (@lem5440726)). Qed.
Lemma lem5440728 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5440729 : term743 = term744.
Proof. exact (MK_COMB (@lem5440728) (@lem5440727)). Qed.
Lemma lem5440730 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem5440731 : term745 = term711.
Proof. exact (MK_COMB (@lem5440729) (@lem5440730)). Qed.
Lemma lem5440733 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5440734 : term711 = term214.
Proof. exact (@lem5440733 term228). Qed.
Lemma lem5440735 : term745 = term214.
Proof. exact (TRANS (@lem5440731) (@lem5440734)). Qed.
Lemma lem5440737 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5440738 : term303 = term304.
Proof. exact (@lem5440737 term228 term228). Qed.
Lemma lem5440739 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5440740 : term306 = term228.
Proof. exact (EQ_MP (@lem5440739) (@lem940073)). Qed.
Lemma lem5440741 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5440742 : term304 = term227.
Proof. exact (MK_COMB (@lem5440741) (@lem5440740)). Qed.
Lemma lem5440743 : term303 = term227.
Proof. exact (TRANS (@lem5440738) (@lem5440742)). Qed.
Lemma lem5440744 : term744 = term744.
Proof. exact (eq_refl term744). Qed.
Lemma lem5440745 : term746 = term711.
Proof. exact (MK_COMB (@lem5440744) (@lem5440743)). Qed.
Lemma lem5440747 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5440748 : term711 = term214.
Proof. exact (@lem5440747 term228). Qed.
Lemma lem5440749 : term746 = term214.
Proof. exact (TRANS (@lem5440745) (@lem5440748)). Qed.
Lemma lem5440750 : term214 = term746.
Proof. exact (SYM (@lem5440749)). Qed.
Lemma lem5440751 : term745 = term746.
Proof. exact (TRANS (@lem5440735) (@lem5440750)). Qed.
Lemma lem5440752 : term735 = term291.
Proof. exact (@lem5440702 (@lem5440751)). Qed.
Lemma lem5440753 : term734 = term291.
Proof. exact (TRANS (@lem5440668) (@lem5440752)). Qed.
Lemma lem5440755 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5440756 : term291 = term214.
Proof. exact (@lem5440755 term214). Qed.
Lemma lem5440757 : term734 = term214.
Proof. exact (TRANS (@lem5440753) (@lem5440756)). Qed.
Lemma lem5440758 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5440759 : term747 = term744.
Proof. exact (MK_COMB (@lem5440758) (@lem5440757)). Qed.
Lemma lem5440760 (_70508 : int) : (real_of_int _70508) = (real_of_int _70508).
Proof. exact (eq_refl (real_of_int _70508)). Qed.
Lemma lem5440761 (_70508 : int) : (term731 _70508) = (term748 _70508).
Proof. exact (MK_COMB (@lem5440759) (@lem5440760 _70508)). Qed.
Lemma lem5440762 (_70508 : int) : (term753 _70508) = (term748 _70508).
Proof. exact (TRANS (@lem5440659 _70508) (@lem5440761 _70508)). Qed.
Lemma lem5440763 (_70508 : int) : (term748 _70508) = term214.
Proof. exact (@lem1982719 (real_of_int _70508)). Qed.
Lemma lem5440764 (_70508 : int) : (term753 _70508) = term214.
Proof. exact (TRANS (@lem5440762 _70508) (@lem5440763 _70508)). Qed.
Lemma lem5440765 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5440766 (_70508 : int) : (term754 _70508) = term750.
Proof. exact (MK_COMB (@lem5440765) (@lem5440764 _70508)). Qed.
Lemma lem5440767 : term294 = term294.
Proof. exact (eq_refl term294). Qed.
Lemma lem5440768 (_70508 : int) : (term752 _70508) = term755.
Proof. exact (MK_COMB (@lem5440766 _70508) (@lem5440767)). Qed.
Lemma lem5440769 (_70508 : int) : (term786 _70508) = term755.
Proof. exact (TRANS (@lem5440658 _70508) (@lem5440768 _70508)). Qed.
Lemma lem5440770 : term755 = term294.
Proof. exact (@lem1982721 term294). Qed.
Lemma lem5440771 (_70508 : int) : (term786 _70508) = term294.
Proof. exact (TRANS (@lem5440769 _70508) (@lem5440770)). Qed.
Lemma lem5440772 (_70505 : int) (_70508 : int) : (term784 _70505 _70508) = term755.
Proof. exact (MK_COMB (@lem5440657 _70505) (@lem5440771 _70508)). Qed.
Lemma lem5440773 (_70505 : int) (_70508 : int) : (term783 _70505 _70508) = term755.
Proof. exact (TRANS (@lem5440549 _70505 _70508) (@lem5440772 _70505 _70508)). Qed.
Lemma lem5440774 : term755 = term294.
Proof. exact (@lem1982721 term294). Qed.
Lemma lem5440775 (_70505 : int) (_70508 : int) : (term783 _70505 _70508) = term294.
Proof. exact (TRANS (@lem5440773 _70505 _70508) (@lem5440774)). Qed.
Lemma lem5440776 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5440777 (_70505 : int) (_70508 : int) : (term787 _70505 _70508) = term757.
Proof. exact (MK_COMB (@lem5440776) (@lem5440775 _70505 _70508)). Qed.
Lemma lem5440778 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5440779 (_70505 : int) (_70508 : int) : (term782 _70505 _70508) = term758.
Proof. exact (MK_COMB (@lem5440777 _70505 _70508) (@lem5440778)). Qed.
Lemma lem5440780 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term552 _70504 _70506 _70505 _70507 _70508) : term758.
Proof. exact (EQ_MP (@lem5440779 _70505 _70508) (@lem5440548 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440782 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5440783 : term758 = term759.
Proof. exact (@lem5440782 term214 term294). Qed.
Lemma lem5440785 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5440786 : term294 = term295.
Proof. exact (@lem5440785 term228). Qed.
Lemma lem5440788 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5440789 : term214 = term291.
Proof. exact (@lem5440788 (NUMERAL 0)). Qed.
Lemma lem5440790 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5440791 : term216 = term760.
Proof. exact (MK_COMB (@lem5440790) (@lem5440789)). Qed.
Lemma lem5440792 : term759 = term761.
Proof. exact (MK_COMB (@lem5440791) (@lem5440786)). Qed.
Lemma lem5440793 : term762.
Proof. exact (@lem1980026 term214 term227 term294 term227). Qed.
Lemma lem5440795 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440796 : term700 = term706.
Proof. exact (@lem5440795 (NUMERAL 0) term228). Qed.
Lemma lem5440797 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440798 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440799 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440798 h1) (fun h1 : term706 = True => @lem5440797)). Qed.
Lemma lem5440800 : term706 = True.
Proof. exact (EQ_MP (@lem5440799) (@lem5440797)). Qed.
Lemma lem5440801 : term700 = True.
Proof. exact (TRANS (@lem5440796) (@lem5440800)). Qed.
Lemma lem5440802 : True = term700.
Proof. exact (SYM (@lem5440801)). Qed.
Lemma lem5440803 : term700.
Proof. exact (EQ_MP (@lem5440802) (@lem0)). Qed.
Lemma lem5440804 : term763.
Proof. exact (@lem5440793 (@lem5440803)). Qed.
Lemma lem5440806 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440807 : term700 = term706.
Proof. exact (@lem5440806 (NUMERAL 0) term228). Qed.
Lemma lem5440808 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440809 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440810 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440809 h1) (fun h1 : term706 = True => @lem5440808)). Qed.
Lemma lem5440811 : term706 = True.
Proof. exact (EQ_MP (@lem5440810) (@lem5440808)). Qed.
Lemma lem5440812 : term700 = True.
Proof. exact (TRANS (@lem5440807) (@lem5440811)). Qed.
Lemma lem5440813 : True = term700.
Proof. exact (SYM (@lem5440812)). Qed.
Lemma lem5440814 : term700.
Proof. exact (EQ_MP (@lem5440813) (@lem0)). Qed.
Lemma lem5440815 : term761 = term764.
Proof. exact (@lem5440804 (@lem5440814)). Qed.
Lemma lem5440817 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5440818 : term321 = term326.
Proof. exact (@lem5440817 term228 term228). Qed.
Lemma lem5440819 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5440820 : term306 = term228.
Proof. exact (EQ_MP (@lem5440819) (@lem940073)). Qed.
Lemma lem5440821 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5440822 : term304 = term227.
Proof. exact (MK_COMB (@lem5440821) (@lem5440820)). Qed.
Lemma lem5440823 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5440824 : term326 = term294.
Proof. exact (MK_COMB (@lem5440823) (@lem5440822)). Qed.
Lemma lem5440825 : term321 = term294.
Proof. exact (TRANS (@lem5440818) (@lem5440824)). Qed.
Lemma lem5440827 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5440828 : term711 = term214.
Proof. exact (@lem5440827 term228). Qed.
Lemma lem5440829 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5440830 : term765 = term216.
Proof. exact (MK_COMB (@lem5440829) (@lem5440828)). Qed.
Lemma lem5440831 : term764 = term759.
Proof. exact (MK_COMB (@lem5440830) (@lem5440825)). Qed.
Lemma lem5440833 (m : nat) (n : nat) : (term766 m n) = (term767 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5440834 : term759 = term768.
Proof. exact (@lem5440833 (NUMERAL 0) term228). Qed.
Lemma lem5440835 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440836 (h1 : term707 = (BIT1 0)) : (term228 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5440837 : (term707 = (BIT1 0)) = ((term228 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440836 h1) (fun h1 : (term228 = (NUMERAL 0)) = False => @lem5440835)). Qed.
Lemma lem5440838 : (term228 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5440837) (@lem5440835)). Qed.
Lemma lem5440839 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5440840 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5440841 : term769 = (and True).
Proof. exact (MK_COMB (@lem5440840) (@lem5440839)). Qed.
Lemma lem5440842 : term768 = (True /\ False).
Proof. exact (MK_COMB (@lem5440841) (@lem5440838)). Qed.
Lemma lem5440844 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5440845 : term768 = False.
Proof. exact (TRANS (@lem5440842) (@lem5440844)). Qed.
Lemma lem5440846 : term759 = False.
Proof. exact (TRANS (@lem5440834) (@lem5440845)). Qed.
Lemma lem5440847 : term764 = False.
Proof. exact (TRANS (@lem5440831) (@lem5440846)). Qed.
Lemma lem5440848 : term761 = False.
Proof. exact (TRANS (@lem5440815) (@lem5440847)). Qed.
Lemma lem5440849 : term759 = False.
Proof. exact (TRANS (@lem5440792) (@lem5440848)). Qed.
Lemma lem5440850 : term758 = False.
Proof. exact (TRANS (@lem5440783) (@lem5440849)). Qed.
Lemma lem5440851 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term552 _70504 _70506 _70505 _70507 _70508) : False.
Proof. exact (EQ_MP (@lem5440850) (@lem5440780 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440852 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term555 _70504 _70506 _70505 _70507 _70508) : False.
Proof. exact (or_elim (@lem5439901 _70504 _70506 _70505 _70507 _70508 h1) (fun h0 : term544 _70504 _70506 _70505 _70507 _70508 => @lem5440376 _70504 _70506 _70505 _70507 _70508 h0) (fun h0 : term552 _70504 _70506 _70505 _70507 _70508 => @lem5440851 _70504 _70506 _70505 _70507 _70508 h0)). Qed.
Lemma lem5440853 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term572 _70504 _70506 _70505 _70507 _70508) : term572 _70504 _70506 _70505 _70507 _70508.
Proof. exact (h1). Qed.
Lemma lem5440854 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term562 _70504 _70506 _70505 _70507 _70508) : term562 _70504 _70506 _70505 _70507 _70508.
Proof. exact (h1). Qed.
Lemma lem5440855 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term562 _70504 _70506 _70505 _70507 _70508) : term560 _70504 _70506 _70505 _70507 _70508.
Proof. exact (proj2 (@lem5440854 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440857 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term562 _70504 _70506 _70505 _70507 _70508) : term559 _70504 _70506 _70505 _70507 _70508.
Proof. exact (proj2 (@lem5440855 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440859 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term562 _70504 _70506 _70505 _70507 _70508) : term558 _70504 _70506 _70505 _70507 _70508.
Proof. exact (proj2 (@lem5440857 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440861 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term562 _70504 _70506 _70505 _70507 _70508) : term557 _70504 _70506 _70505 _70507 _70508.
Proof. exact (proj2 (@lem5440859 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440863 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term562 _70504 _70506 _70505 _70507 _70508) : term556 _70504 _70506 _70505 _70507 _70508.
Proof. exact (proj2 (@lem5440861 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440865 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term562 _70504 _70506 _70505 _70507 _70508) : term536 _70504 _70506 _70505 _70507 _70508.
Proof. exact (proj2 (@lem5440863 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440866 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term562 _70504 _70506 _70505 _70507 _70508) : term334 _70506 _70508.
Proof. exact (proj1 (@lem5440863 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440868 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term562 _70504 _70506 _70505 _70507 _70508) : term530 _70504 _70506 _70508.
Proof. exact (proj1 (@lem5440865 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440869 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term562 _70504 _70506 _70505 _70507 _70508) : term366 _70506 _70508.
Proof. exact (proj2 (@lem5440868 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440874 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5440875 : term699 = term700.
Proof. exact (@lem5440874 term214 term227). Qed.
Lemma lem5440877 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5440878 : term227 = term320.
Proof. exact (@lem5440877 term228). Qed.
Lemma lem5440880 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5440881 : term214 = term291.
Proof. exact (@lem5440880 (NUMERAL 0)). Qed.
Lemma lem5440882 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5440883 : term701 = term702.
Proof. exact (MK_COMB (@lem5440882) (@lem5440881)). Qed.
Lemma lem5440884 : term700 = term703.
Proof. exact (MK_COMB (@lem5440883) (@lem5440878)). Qed.
Lemma lem5440885 : term704.
Proof. exact (@lem1980255 term214 term227 term227 term227). Qed.
Lemma lem5440887 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440888 : term700 = term706.
Proof. exact (@lem5440887 (NUMERAL 0) term228). Qed.
Lemma lem5440889 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440890 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440891 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440890 h1) (fun h1 : term706 = True => @lem5440889)). Qed.
Lemma lem5440892 : term706 = True.
Proof. exact (EQ_MP (@lem5440891) (@lem5440889)). Qed.
Lemma lem5440893 : term700 = True.
Proof. exact (TRANS (@lem5440888) (@lem5440892)). Qed.
Lemma lem5440894 : True = term700.
Proof. exact (SYM (@lem5440893)). Qed.
Lemma lem5440895 : term700.
Proof. exact (EQ_MP (@lem5440894) (@lem0)). Qed.
Lemma lem5440896 : term708.
Proof. exact (@lem5440885 (@lem5440895)). Qed.
Lemma lem5440898 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440899 : term700 = term706.
Proof. exact (@lem5440898 (NUMERAL 0) term228). Qed.
Lemma lem5440900 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440901 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440902 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440901 h1) (fun h1 : term706 = True => @lem5440900)). Qed.
Lemma lem5440903 : term706 = True.
Proof. exact (EQ_MP (@lem5440902) (@lem5440900)). Qed.
Lemma lem5440904 : term700 = True.
Proof. exact (TRANS (@lem5440899) (@lem5440903)). Qed.
Lemma lem5440905 : True = term700.
Proof. exact (SYM (@lem5440904)). Qed.
Lemma lem5440906 : term700.
Proof. exact (EQ_MP (@lem5440905) (@lem0)). Qed.
Lemma lem5440907 : term703 = term709.
Proof. exact (@lem5440896 (@lem5440906)). Qed.
Lemma lem5440909 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5440910 : term303 = term304.
Proof. exact (@lem5440909 term228 term228). Qed.
Lemma lem5440911 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5440912 : term306 = term228.
Proof. exact (EQ_MP (@lem5440911) (@lem940073)). Qed.
Lemma lem5440913 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5440914 : term304 = term227.
Proof. exact (MK_COMB (@lem5440913) (@lem5440912)). Qed.
Lemma lem5440915 : term303 = term227.
Proof. exact (TRANS (@lem5440910) (@lem5440914)). Qed.
Lemma lem5440917 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5440918 : term711 = term214.
Proof. exact (@lem5440917 term228). Qed.
Lemma lem5440919 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5440920 : term712 = term701.
Proof. exact (MK_COMB (@lem5440919) (@lem5440918)). Qed.
Lemma lem5440921 : term709 = term700.
Proof. exact (MK_COMB (@lem5440920) (@lem5440915)). Qed.
Lemma lem5440923 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440924 : term700 = term706.
Proof. exact (@lem5440923 (NUMERAL 0) term228). Qed.
Lemma lem5440925 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440926 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440927 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440926 h1) (fun h1 : term706 = True => @lem5440925)). Qed.
Lemma lem5440928 : term706 = True.
Proof. exact (EQ_MP (@lem5440927) (@lem5440925)). Qed.
Lemma lem5440929 : term700 = True.
Proof. exact (TRANS (@lem5440924) (@lem5440928)). Qed.
Lemma lem5440930 : term709 = True.
Proof. exact (TRANS (@lem5440921) (@lem5440929)). Qed.
Lemma lem5440931 : term703 = True.
Proof. exact (TRANS (@lem5440907) (@lem5440930)). Qed.
Lemma lem5440932 : term700 = True.
Proof. exact (TRANS (@lem5440884) (@lem5440931)). Qed.
Lemma lem5440933 : term699 = True.
Proof. exact (TRANS (@lem5440875) (@lem5440932)). Qed.
Lemma lem5440934 : True = term699.
Proof. exact (SYM (@lem5440933)). Qed.
Lemma lem5440935 : term699.
Proof. exact (EQ_MP (@lem5440934) (@lem0)). Qed.
Lemma lem5440936 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term562 _70504 _70506 _70505 _70507 _70508) : term713 _70506 _70508.
Proof. exact (conj (@lem5440935) (@lem5440866 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440938 (x : real) (y : real) : term714 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5440939 (_70506 : int) (_70508 : int) : term715 _70506 _70508.
Proof. exact (@lem5440938 term227 (term331 _70506 _70508)). Qed.
Lemma lem5440940 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term562 _70504 _70506 _70505 _70507 _70508) : term716 _70506 _70508.
Proof. exact (@lem5440939 _70506 _70508 (@lem5440936 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440941 (_70506 : int) (_70508 : int) : (term717 _70506 _70508) = (term331 _70506 _70508).
Proof. exact (@lem1982733 (term331 _70506 _70508)). Qed.
Lemma lem5440942 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5440943 (_70506 : int) (_70508 : int) : (term718 _70506 _70508) = (term333 _70506 _70508).
Proof. exact (MK_COMB (@lem5440942) (@lem5440941 _70506 _70508)). Qed.
Lemma lem5440944 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5440945 (_70506 : int) (_70508 : int) : (term716 _70506 _70508) = (term334 _70506 _70508).
Proof. exact (MK_COMB (@lem5440943 _70506 _70508) (@lem5440944)). Qed.
Lemma lem5440946 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term562 _70504 _70506 _70505 _70507 _70508) : term334 _70506 _70508.
Proof. exact (EQ_MP (@lem5440945 _70506 _70508) (@lem5440940 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5440948 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5440949 : term699 = term700.
Proof. exact (@lem5440948 term214 term227). Qed.
Lemma lem5440951 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5440952 : term227 = term320.
Proof. exact (@lem5440951 term228). Qed.
Lemma lem5440954 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5440955 : term214 = term291.
Proof. exact (@lem5440954 (NUMERAL 0)). Qed.
Lemma lem5440956 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5440957 : term701 = term702.
Proof. exact (MK_COMB (@lem5440956) (@lem5440955)). Qed.
Lemma lem5440958 : term700 = term703.
Proof. exact (MK_COMB (@lem5440957) (@lem5440952)). Qed.
Lemma lem5440959 : term704.
Proof. exact (@lem1980255 term214 term227 term227 term227). Qed.
Lemma lem5440961 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440962 : term700 = term706.
Proof. exact (@lem5440961 (NUMERAL 0) term228). Qed.
Lemma lem5440963 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440964 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440965 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440964 h1) (fun h1 : term706 = True => @lem5440963)). Qed.
Lemma lem5440966 : term706 = True.
Proof. exact (EQ_MP (@lem5440965) (@lem5440963)). Qed.
Lemma lem5440967 : term700 = True.
Proof. exact (TRANS (@lem5440962) (@lem5440966)). Qed.
Lemma lem5440968 : True = term700.
Proof. exact (SYM (@lem5440967)). Qed.
Lemma lem5440969 : term700.
Proof. exact (EQ_MP (@lem5440968) (@lem0)). Qed.
Lemma lem5440970 : term708.
Proof. exact (@lem5440959 (@lem5440969)). Qed.
Lemma lem5440972 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440973 : term700 = term706.
Proof. exact (@lem5440972 (NUMERAL 0) term228). Qed.
Lemma lem5440974 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5440975 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5440976 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5440975 h1) (fun h1 : term706 = True => @lem5440974)). Qed.
Lemma lem5440977 : term706 = True.
Proof. exact (EQ_MP (@lem5440976) (@lem5440974)). Qed.
Lemma lem5440978 : term700 = True.
Proof. exact (TRANS (@lem5440973) (@lem5440977)). Qed.
Lemma lem5440979 : True = term700.
Proof. exact (SYM (@lem5440978)). Qed.
Lemma lem5440980 : term700.
Proof. exact (EQ_MP (@lem5440979) (@lem0)). Qed.
Lemma lem5440981 : term703 = term709.
Proof. exact (@lem5440970 (@lem5440980)). Qed.
Lemma lem5440983 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5440984 : term303 = term304.
Proof. exact (@lem5440983 term228 term228). Qed.
Lemma lem5440985 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5440986 : term306 = term228.
Proof. exact (EQ_MP (@lem5440985) (@lem940073)). Qed.
Lemma lem5440987 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5440988 : term304 = term227.
Proof. exact (MK_COMB (@lem5440987) (@lem5440986)). Qed.
Lemma lem5440989 : term303 = term227.
Proof. exact (TRANS (@lem5440984) (@lem5440988)). Qed.
Lemma lem5440991 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5440992 : term711 = term214.
Proof. exact (@lem5440991 term228). Qed.
Lemma lem5440993 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5440994 : term712 = term701.
Proof. exact (MK_COMB (@lem5440993) (@lem5440992)). Qed.
Lemma lem5440995 : term709 = term700.
Proof. exact (MK_COMB (@lem5440994) (@lem5440989)). Qed.
Lemma lem5440997 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5440998 : term700 = term706.
Proof. exact (@lem5440997 (NUMERAL 0) term228). Qed.
Lemma lem5440999 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441000 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441001 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441000 h1) (fun h1 : term706 = True => @lem5440999)). Qed.
Lemma lem5441002 : term706 = True.
Proof. exact (EQ_MP (@lem5441001) (@lem5440999)). Qed.
Lemma lem5441003 : term700 = True.
Proof. exact (TRANS (@lem5440998) (@lem5441002)). Qed.
Lemma lem5441004 : term709 = True.
Proof. exact (TRANS (@lem5440995) (@lem5441003)). Qed.
Lemma lem5441005 : term703 = True.
Proof. exact (TRANS (@lem5440981) (@lem5441004)). Qed.
Lemma lem5441006 : term700 = True.
Proof. exact (TRANS (@lem5440958) (@lem5441005)). Qed.
Lemma lem5441007 : term699 = True.
Proof. exact (TRANS (@lem5440949) (@lem5441006)). Qed.
Lemma lem5441008 : True = term699.
Proof. exact (SYM (@lem5441007)). Qed.
Lemma lem5441009 : term699.
Proof. exact (EQ_MP (@lem5441008) (@lem0)). Qed.
Lemma lem5441010 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term562 _70504 _70506 _70505 _70507 _70508) : term719 _70506 _70508.
Proof. exact (conj (@lem5441009) (@lem5440869 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5441012 (x : real) (y : real) : term714 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5441013 (_70506 : int) (_70508 : int) : term720 _70506 _70508.
Proof. exact (@lem5441012 term227 (term363 _70506 _70508)). Qed.
Lemma lem5441014 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term562 _70504 _70506 _70505 _70507 _70508) : term721 _70506 _70508.
Proof. exact (@lem5441013 _70506 _70508 (@lem5441010 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5441015 (_70506 : int) (_70508 : int) : (term722 _70506 _70508) = (term363 _70506 _70508).
Proof. exact (@lem1982733 (term363 _70506 _70508)). Qed.
Lemma lem5441016 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5441017 (_70506 : int) (_70508 : int) : (term723 _70506 _70508) = (term365 _70506 _70508).
Proof. exact (MK_COMB (@lem5441016) (@lem5441015 _70506 _70508)). Qed.
Lemma lem5441018 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5441019 (_70506 : int) (_70508 : int) : (term721 _70506 _70508) = (term366 _70506 _70508).
Proof. exact (MK_COMB (@lem5441017 _70506 _70508) (@lem5441018)). Qed.
Lemma lem5441020 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term562 _70504 _70506 _70505 _70507 _70508) : term366 _70506 _70508.
Proof. exact (EQ_MP (@lem5441019 _70506 _70508) (@lem5441014 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5441021 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term562 _70504 _70506 _70505 _70507 _70508) : term724 _70506 _70508.
Proof. exact (conj (@lem5441020 _70504 _70506 _70505 _70507 _70508 h1) (@lem5440946 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5441023 (x : real) (y : real) : term725 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5441024 (_70506 : int) (_70508 : int) : term726 _70506 _70508.
Proof. exact (@lem5441023 (term363 _70506 _70508) (term331 _70506 _70508)). Qed.
Lemma lem5441025 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term562 _70504 _70506 _70505 _70507 _70508) : term727 _70506 _70508.
Proof. exact (@lem5441024 _70506 _70508 (@lem5441021 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5441026 (_70506 : int) (_70508 : int) : (term728 _70506 _70508) = (term729 _70506 _70508).
Proof. exact (@lem1982753 (term336 _70506) (real_of_int _70506) (real_of_int _70508) (term330 _70508)). Qed.
Lemma lem5441027 (_70506 : int) : (term730 _70506) = (term731 _70506).
Proof. exact (@lem1982713 term294 (real_of_int _70506)). Qed.
Lemma lem5441029 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5441030 : term227 = term320.
Proof. exact (@lem5441029 term228). Qed.
Lemma lem5441032 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5441033 : term294 = term295.
Proof. exact (@lem5441032 term228). Qed.
Lemma lem5441034 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5441035 : term732 = term733.
Proof. exact (MK_COMB (@lem5441034) (@lem5441033)). Qed.
Lemma lem5441036 : term734 = term735.
Proof. exact (MK_COMB (@lem5441035) (@lem5441030)). Qed.
Lemma lem5441037 : term736.
Proof. exact (@lem1981473 term294 term227 term227 term227 term214 term227). Qed.
Lemma lem5441039 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441040 : term700 = term706.
Proof. exact (@lem5441039 (NUMERAL 0) term228). Qed.
Lemma lem5441041 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441042 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441043 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441042 h1) (fun h1 : term706 = True => @lem5441041)). Qed.
Lemma lem5441044 : term706 = True.
Proof. exact (EQ_MP (@lem5441043) (@lem5441041)). Qed.
Lemma lem5441045 : term700 = True.
Proof. exact (TRANS (@lem5441040) (@lem5441044)). Qed.
Lemma lem5441046 : True = term700.
Proof. exact (SYM (@lem5441045)). Qed.
Lemma lem5441047 : term700.
Proof. exact (EQ_MP (@lem5441046) (@lem0)). Qed.
Lemma lem5441048 : term737.
Proof. exact (@lem5441037 (@lem5441047)). Qed.
Lemma lem5441050 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441051 : term700 = term706.
Proof. exact (@lem5441050 (NUMERAL 0) term228). Qed.
Lemma lem5441052 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441053 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441054 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441053 h1) (fun h1 : term706 = True => @lem5441052)). Qed.
Lemma lem5441055 : term706 = True.
Proof. exact (EQ_MP (@lem5441054) (@lem5441052)). Qed.
Lemma lem5441056 : term700 = True.
Proof. exact (TRANS (@lem5441051) (@lem5441055)). Qed.
Lemma lem5441057 : True = term700.
Proof. exact (SYM (@lem5441056)). Qed.
Lemma lem5441058 : term700.
Proof. exact (EQ_MP (@lem5441057) (@lem0)). Qed.
Lemma lem5441059 : term738.
Proof. exact (@lem5441048 (@lem5441058)). Qed.
Lemma lem5441061 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441062 : term700 = term706.
Proof. exact (@lem5441061 (NUMERAL 0) term228). Qed.
Lemma lem5441063 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441064 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441065 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441064 h1) (fun h1 : term706 = True => @lem5441063)). Qed.
Lemma lem5441066 : term706 = True.
Proof. exact (EQ_MP (@lem5441065) (@lem5441063)). Qed.
Lemma lem5441067 : term700 = True.
Proof. exact (TRANS (@lem5441062) (@lem5441066)). Qed.
Lemma lem5441068 : True = term700.
Proof. exact (SYM (@lem5441067)). Qed.
Lemma lem5441069 : term700.
Proof. exact (EQ_MP (@lem5441068) (@lem0)). Qed.
Lemma lem5441070 : term739.
Proof. exact (@lem5441059 (@lem5441069)). Qed.
Lemma lem5441072 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5441073 : term303 = term304.
Proof. exact (@lem5441072 term228 term228). Qed.
Lemma lem5441074 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5441075 : term306 = term228.
Proof. exact (EQ_MP (@lem5441074) (@lem940073)). Qed.
Lemma lem5441076 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5441077 : term304 = term227.
Proof. exact (MK_COMB (@lem5441076) (@lem5441075)). Qed.
Lemma lem5441078 : term303 = term227.
Proof. exact (TRANS (@lem5441073) (@lem5441077)). Qed.
Lemma lem5441080 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5441081 : term321 = term326.
Proof. exact (@lem5441080 term228 term228). Qed.
Lemma lem5441082 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5441083 : term306 = term228.
Proof. exact (EQ_MP (@lem5441082) (@lem940073)). Qed.
Lemma lem5441084 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5441085 : term304 = term227.
Proof. exact (MK_COMB (@lem5441084) (@lem5441083)). Qed.
Lemma lem5441086 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5441087 : term326 = term294.
Proof. exact (MK_COMB (@lem5441086) (@lem5441085)). Qed.
Lemma lem5441088 : term321 = term294.
Proof. exact (TRANS (@lem5441081) (@lem5441087)). Qed.
Lemma lem5441089 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5441090 : term740 = term732.
Proof. exact (MK_COMB (@lem5441089) (@lem5441088)). Qed.
Lemma lem5441091 : term741 = term734.
Proof. exact (MK_COMB (@lem5441090) (@lem5441078)). Qed.
Lemma lem5441093 (m : nat) : (term742 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5441094 : term734 = term214.
Proof. exact (@lem5441093 term228). Qed.
Lemma lem5441095 : term741 = term214.
Proof. exact (TRANS (@lem5441091) (@lem5441094)). Qed.
Lemma lem5441096 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5441097 : term743 = term744.
Proof. exact (MK_COMB (@lem5441096) (@lem5441095)). Qed.
Lemma lem5441098 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem5441099 : term745 = term711.
Proof. exact (MK_COMB (@lem5441097) (@lem5441098)). Qed.
Lemma lem5441101 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5441102 : term711 = term214.
Proof. exact (@lem5441101 term228). Qed.
Lemma lem5441103 : term745 = term214.
Proof. exact (TRANS (@lem5441099) (@lem5441102)). Qed.
Lemma lem5441105 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5441106 : term303 = term304.
Proof. exact (@lem5441105 term228 term228). Qed.
Lemma lem5441107 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5441108 : term306 = term228.
Proof. exact (EQ_MP (@lem5441107) (@lem940073)). Qed.
Lemma lem5441109 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5441110 : term304 = term227.
Proof. exact (MK_COMB (@lem5441109) (@lem5441108)). Qed.
Lemma lem5441111 : term303 = term227.
Proof. exact (TRANS (@lem5441106) (@lem5441110)). Qed.
Lemma lem5441112 : term744 = term744.
Proof. exact (eq_refl term744). Qed.
Lemma lem5441113 : term746 = term711.
Proof. exact (MK_COMB (@lem5441112) (@lem5441111)). Qed.
Lemma lem5441115 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5441116 : term711 = term214.
Proof. exact (@lem5441115 term228). Qed.
Lemma lem5441117 : term746 = term214.
Proof. exact (TRANS (@lem5441113) (@lem5441116)). Qed.
Lemma lem5441118 : term214 = term746.
Proof. exact (SYM (@lem5441117)). Qed.
Lemma lem5441119 : term745 = term746.
Proof. exact (TRANS (@lem5441103) (@lem5441118)). Qed.
Lemma lem5441120 : term735 = term291.
Proof. exact (@lem5441070 (@lem5441119)). Qed.
Lemma lem5441121 : term734 = term291.
Proof. exact (TRANS (@lem5441036) (@lem5441120)). Qed.
Lemma lem5441123 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5441124 : term291 = term214.
Proof. exact (@lem5441123 term214). Qed.
Lemma lem5441125 : term734 = term214.
Proof. exact (TRANS (@lem5441121) (@lem5441124)). Qed.
Lemma lem5441126 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5441127 : term747 = term744.
Proof. exact (MK_COMB (@lem5441126) (@lem5441125)). Qed.
Lemma lem5441128 (_70506 : int) : (real_of_int _70506) = (real_of_int _70506).
Proof. exact (eq_refl (real_of_int _70506)). Qed.
Lemma lem5441129 (_70506 : int) : (term731 _70506) = (term748 _70506).
Proof. exact (MK_COMB (@lem5441127) (@lem5441128 _70506)). Qed.
Lemma lem5441130 (_70506 : int) : (term730 _70506) = (term748 _70506).
Proof. exact (TRANS (@lem5441027 _70506) (@lem5441129 _70506)). Qed.
Lemma lem5441131 (_70506 : int) : (term748 _70506) = term214.
Proof. exact (@lem1982719 (real_of_int _70506)). Qed.
Lemma lem5441132 (_70506 : int) : (term730 _70506) = term214.
Proof. exact (TRANS (@lem5441130 _70506) (@lem5441131 _70506)). Qed.
Lemma lem5441133 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5441134 (_70506 : int) : (term749 _70506) = term750.
Proof. exact (MK_COMB (@lem5441133) (@lem5441132 _70506)). Qed.
Lemma lem5441135 (_70508 : int) : (term751 _70508) = (term752 _70508).
Proof. exact (@lem1982763 (real_of_int _70508) (term336 _70508) term294). Qed.
Lemma lem5441136 (_70508 : int) : (term753 _70508) = (term731 _70508).
Proof. exact (@lem1982715 term294 (real_of_int _70508)). Qed.
Lemma lem5441138 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5441139 : term227 = term320.
Proof. exact (@lem5441138 term228). Qed.
Lemma lem5441141 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5441142 : term294 = term295.
Proof. exact (@lem5441141 term228). Qed.
Lemma lem5441143 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5441144 : term732 = term733.
Proof. exact (MK_COMB (@lem5441143) (@lem5441142)). Qed.
Lemma lem5441145 : term734 = term735.
Proof. exact (MK_COMB (@lem5441144) (@lem5441139)). Qed.
Lemma lem5441146 : term736.
Proof. exact (@lem1981473 term294 term227 term227 term227 term214 term227). Qed.
Lemma lem5441148 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441149 : term700 = term706.
Proof. exact (@lem5441148 (NUMERAL 0) term228). Qed.
Lemma lem5441150 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441151 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441152 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441151 h1) (fun h1 : term706 = True => @lem5441150)). Qed.
Lemma lem5441153 : term706 = True.
Proof. exact (EQ_MP (@lem5441152) (@lem5441150)). Qed.
Lemma lem5441154 : term700 = True.
Proof. exact (TRANS (@lem5441149) (@lem5441153)). Qed.
Lemma lem5441155 : True = term700.
Proof. exact (SYM (@lem5441154)). Qed.
Lemma lem5441156 : term700.
Proof. exact (EQ_MP (@lem5441155) (@lem0)). Qed.
Lemma lem5441157 : term737.
Proof. exact (@lem5441146 (@lem5441156)). Qed.
Lemma lem5441159 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441160 : term700 = term706.
Proof. exact (@lem5441159 (NUMERAL 0) term228). Qed.
Lemma lem5441161 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441162 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441163 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441162 h1) (fun h1 : term706 = True => @lem5441161)). Qed.
Lemma lem5441164 : term706 = True.
Proof. exact (EQ_MP (@lem5441163) (@lem5441161)). Qed.
Lemma lem5441165 : term700 = True.
Proof. exact (TRANS (@lem5441160) (@lem5441164)). Qed.
Lemma lem5441166 : True = term700.
Proof. exact (SYM (@lem5441165)). Qed.
Lemma lem5441167 : term700.
Proof. exact (EQ_MP (@lem5441166) (@lem0)). Qed.
Lemma lem5441168 : term738.
Proof. exact (@lem5441157 (@lem5441167)). Qed.
Lemma lem5441170 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441171 : term700 = term706.
Proof. exact (@lem5441170 (NUMERAL 0) term228). Qed.
Lemma lem5441172 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441173 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441174 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441173 h1) (fun h1 : term706 = True => @lem5441172)). Qed.
Lemma lem5441175 : term706 = True.
Proof. exact (EQ_MP (@lem5441174) (@lem5441172)). Qed.
Lemma lem5441176 : term700 = True.
Proof. exact (TRANS (@lem5441171) (@lem5441175)). Qed.
Lemma lem5441177 : True = term700.
Proof. exact (SYM (@lem5441176)). Qed.
Lemma lem5441178 : term700.
Proof. exact (EQ_MP (@lem5441177) (@lem0)). Qed.
Lemma lem5441179 : term739.
Proof. exact (@lem5441168 (@lem5441178)). Qed.
Lemma lem5441181 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5441182 : term303 = term304.
Proof. exact (@lem5441181 term228 term228). Qed.
Lemma lem5441183 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5441184 : term306 = term228.
Proof. exact (EQ_MP (@lem5441183) (@lem940073)). Qed.
Lemma lem5441185 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5441186 : term304 = term227.
Proof. exact (MK_COMB (@lem5441185) (@lem5441184)). Qed.
Lemma lem5441187 : term303 = term227.
Proof. exact (TRANS (@lem5441182) (@lem5441186)). Qed.
Lemma lem5441189 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5441190 : term321 = term326.
Proof. exact (@lem5441189 term228 term228). Qed.
Lemma lem5441191 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5441192 : term306 = term228.
Proof. exact (EQ_MP (@lem5441191) (@lem940073)). Qed.
Lemma lem5441193 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5441194 : term304 = term227.
Proof. exact (MK_COMB (@lem5441193) (@lem5441192)). Qed.
Lemma lem5441195 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5441196 : term326 = term294.
Proof. exact (MK_COMB (@lem5441195) (@lem5441194)). Qed.
Lemma lem5441197 : term321 = term294.
Proof. exact (TRANS (@lem5441190) (@lem5441196)). Qed.
Lemma lem5441198 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5441199 : term740 = term732.
Proof. exact (MK_COMB (@lem5441198) (@lem5441197)). Qed.
Lemma lem5441200 : term741 = term734.
Proof. exact (MK_COMB (@lem5441199) (@lem5441187)). Qed.
Lemma lem5441202 (m : nat) : (term742 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5441203 : term734 = term214.
Proof. exact (@lem5441202 term228). Qed.
Lemma lem5441204 : term741 = term214.
Proof. exact (TRANS (@lem5441200) (@lem5441203)). Qed.
Lemma lem5441205 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5441206 : term743 = term744.
Proof. exact (MK_COMB (@lem5441205) (@lem5441204)). Qed.
Lemma lem5441207 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem5441208 : term745 = term711.
Proof. exact (MK_COMB (@lem5441206) (@lem5441207)). Qed.
Lemma lem5441210 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5441211 : term711 = term214.
Proof. exact (@lem5441210 term228). Qed.
Lemma lem5441212 : term745 = term214.
Proof. exact (TRANS (@lem5441208) (@lem5441211)). Qed.
Lemma lem5441214 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5441215 : term303 = term304.
Proof. exact (@lem5441214 term228 term228). Qed.
Lemma lem5441216 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5441217 : term306 = term228.
Proof. exact (EQ_MP (@lem5441216) (@lem940073)). Qed.
Lemma lem5441218 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5441219 : term304 = term227.
Proof. exact (MK_COMB (@lem5441218) (@lem5441217)). Qed.
Lemma lem5441220 : term303 = term227.
Proof. exact (TRANS (@lem5441215) (@lem5441219)). Qed.
Lemma lem5441221 : term744 = term744.
Proof. exact (eq_refl term744). Qed.
Lemma lem5441222 : term746 = term711.
Proof. exact (MK_COMB (@lem5441221) (@lem5441220)). Qed.
Lemma lem5441224 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5441225 : term711 = term214.
Proof. exact (@lem5441224 term228). Qed.
Lemma lem5441226 : term746 = term214.
Proof. exact (TRANS (@lem5441222) (@lem5441225)). Qed.
Lemma lem5441227 : term214 = term746.
Proof. exact (SYM (@lem5441226)). Qed.
Lemma lem5441228 : term745 = term746.
Proof. exact (TRANS (@lem5441212) (@lem5441227)). Qed.
Lemma lem5441229 : term735 = term291.
Proof. exact (@lem5441179 (@lem5441228)). Qed.
Lemma lem5441230 : term734 = term291.
Proof. exact (TRANS (@lem5441145) (@lem5441229)). Qed.
Lemma lem5441232 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5441233 : term291 = term214.
Proof. exact (@lem5441232 term214). Qed.
Lemma lem5441234 : term734 = term214.
Proof. exact (TRANS (@lem5441230) (@lem5441233)). Qed.
Lemma lem5441235 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5441236 : term747 = term744.
Proof. exact (MK_COMB (@lem5441235) (@lem5441234)). Qed.
Lemma lem5441237 (_70508 : int) : (real_of_int _70508) = (real_of_int _70508).
Proof. exact (eq_refl (real_of_int _70508)). Qed.
Lemma lem5441238 (_70508 : int) : (term731 _70508) = (term748 _70508).
Proof. exact (MK_COMB (@lem5441236) (@lem5441237 _70508)). Qed.
Lemma lem5441239 (_70508 : int) : (term753 _70508) = (term748 _70508).
Proof. exact (TRANS (@lem5441136 _70508) (@lem5441238 _70508)). Qed.
Lemma lem5441240 (_70508 : int) : (term748 _70508) = term214.
Proof. exact (@lem1982719 (real_of_int _70508)). Qed.
Lemma lem5441241 (_70508 : int) : (term753 _70508) = term214.
Proof. exact (TRANS (@lem5441239 _70508) (@lem5441240 _70508)). Qed.
Lemma lem5441242 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5441243 (_70508 : int) : (term754 _70508) = term750.
Proof. exact (MK_COMB (@lem5441242) (@lem5441241 _70508)). Qed.
Lemma lem5441244 : term294 = term294.
Proof. exact (eq_refl term294). Qed.
Lemma lem5441245 (_70508 : int) : (term752 _70508) = term755.
Proof. exact (MK_COMB (@lem5441243 _70508) (@lem5441244)). Qed.
Lemma lem5441246 (_70508 : int) : (term751 _70508) = term755.
Proof. exact (TRANS (@lem5441135 _70508) (@lem5441245 _70508)). Qed.
Lemma lem5441247 : term755 = term294.
Proof. exact (@lem1982721 term294). Qed.
Lemma lem5441248 (_70508 : int) : (term751 _70508) = term294.
Proof. exact (TRANS (@lem5441246 _70508) (@lem5441247)). Qed.
Lemma lem5441249 (_70506 : int) (_70508 : int) : (term729 _70506 _70508) = term755.
Proof. exact (MK_COMB (@lem5441134 _70506) (@lem5441248 _70508)). Qed.
Lemma lem5441250 (_70506 : int) (_70508 : int) : (term728 _70506 _70508) = term755.
Proof. exact (TRANS (@lem5441026 _70506 _70508) (@lem5441249 _70506 _70508)). Qed.
Lemma lem5441251 : term755 = term294.
Proof. exact (@lem1982721 term294). Qed.
Lemma lem5441252 (_70506 : int) (_70508 : int) : (term728 _70506 _70508) = term294.
Proof. exact (TRANS (@lem5441250 _70506 _70508) (@lem5441251)). Qed.
Lemma lem5441253 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5441254 (_70506 : int) (_70508 : int) : (term756 _70506 _70508) = term757.
Proof. exact (MK_COMB (@lem5441253) (@lem5441252 _70506 _70508)). Qed.
Lemma lem5441255 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5441256 (_70506 : int) (_70508 : int) : (term727 _70506 _70508) = term758.
Proof. exact (MK_COMB (@lem5441254 _70506 _70508) (@lem5441255)). Qed.
Lemma lem5441257 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term562 _70504 _70506 _70505 _70507 _70508) : term758.
Proof. exact (EQ_MP (@lem5441256 _70506 _70508) (@lem5441025 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5441259 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5441260 : term758 = term759.
Proof. exact (@lem5441259 term214 term294). Qed.
Lemma lem5441262 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5441263 : term294 = term295.
Proof. exact (@lem5441262 term228). Qed.
Lemma lem5441265 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5441266 : term214 = term291.
Proof. exact (@lem5441265 (NUMERAL 0)). Qed.
Lemma lem5441267 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5441268 : term216 = term760.
Proof. exact (MK_COMB (@lem5441267) (@lem5441266)). Qed.
Lemma lem5441269 : term759 = term761.
Proof. exact (MK_COMB (@lem5441268) (@lem5441263)). Qed.
Lemma lem5441270 : term762.
Proof. exact (@lem1980026 term214 term227 term294 term227). Qed.
Lemma lem5441272 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441273 : term700 = term706.
Proof. exact (@lem5441272 (NUMERAL 0) term228). Qed.
Lemma lem5441274 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441275 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441276 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441275 h1) (fun h1 : term706 = True => @lem5441274)). Qed.
Lemma lem5441277 : term706 = True.
Proof. exact (EQ_MP (@lem5441276) (@lem5441274)). Qed.
Lemma lem5441278 : term700 = True.
Proof. exact (TRANS (@lem5441273) (@lem5441277)). Qed.
Lemma lem5441279 : True = term700.
Proof. exact (SYM (@lem5441278)). Qed.
Lemma lem5441280 : term700.
Proof. exact (EQ_MP (@lem5441279) (@lem0)). Qed.
Lemma lem5441281 : term763.
Proof. exact (@lem5441270 (@lem5441280)). Qed.
Lemma lem5441283 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441284 : term700 = term706.
Proof. exact (@lem5441283 (NUMERAL 0) term228). Qed.
Lemma lem5441285 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441286 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441287 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441286 h1) (fun h1 : term706 = True => @lem5441285)). Qed.
Lemma lem5441288 : term706 = True.
Proof. exact (EQ_MP (@lem5441287) (@lem5441285)). Qed.
Lemma lem5441289 : term700 = True.
Proof. exact (TRANS (@lem5441284) (@lem5441288)). Qed.
Lemma lem5441290 : True = term700.
Proof. exact (SYM (@lem5441289)). Qed.
Lemma lem5441291 : term700.
Proof. exact (EQ_MP (@lem5441290) (@lem0)). Qed.
Lemma lem5441292 : term761 = term764.
Proof. exact (@lem5441281 (@lem5441291)). Qed.
Lemma lem5441294 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5441295 : term321 = term326.
Proof. exact (@lem5441294 term228 term228). Qed.
Lemma lem5441296 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5441297 : term306 = term228.
Proof. exact (EQ_MP (@lem5441296) (@lem940073)). Qed.
Lemma lem5441298 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5441299 : term304 = term227.
Proof. exact (MK_COMB (@lem5441298) (@lem5441297)). Qed.
Lemma lem5441300 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5441301 : term326 = term294.
Proof. exact (MK_COMB (@lem5441300) (@lem5441299)). Qed.
Lemma lem5441302 : term321 = term294.
Proof. exact (TRANS (@lem5441295) (@lem5441301)). Qed.
Lemma lem5441304 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5441305 : term711 = term214.
Proof. exact (@lem5441304 term228). Qed.
Lemma lem5441306 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5441307 : term765 = term216.
Proof. exact (MK_COMB (@lem5441306) (@lem5441305)). Qed.
Lemma lem5441308 : term764 = term759.
Proof. exact (MK_COMB (@lem5441307) (@lem5441302)). Qed.
Lemma lem5441310 (m : nat) (n : nat) : (term766 m n) = (term767 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5441311 : term759 = term768.
Proof. exact (@lem5441310 (NUMERAL 0) term228). Qed.
Lemma lem5441312 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441313 (h1 : term707 = (BIT1 0)) : (term228 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5441314 : (term707 = (BIT1 0)) = ((term228 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441313 h1) (fun h1 : (term228 = (NUMERAL 0)) = False => @lem5441312)). Qed.
Lemma lem5441315 : (term228 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5441314) (@lem5441312)). Qed.
Lemma lem5441316 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5441317 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5441318 : term769 = (and True).
Proof. exact (MK_COMB (@lem5441317) (@lem5441316)). Qed.
Lemma lem5441319 : term768 = (True /\ False).
Proof. exact (MK_COMB (@lem5441318) (@lem5441315)). Qed.
Lemma lem5441321 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5441322 : term768 = False.
Proof. exact (TRANS (@lem5441319) (@lem5441321)). Qed.
Lemma lem5441323 : term759 = False.
Proof. exact (TRANS (@lem5441311) (@lem5441322)). Qed.
Lemma lem5441324 : term764 = False.
Proof. exact (TRANS (@lem5441308) (@lem5441323)). Qed.
Lemma lem5441325 : term761 = False.
Proof. exact (TRANS (@lem5441292) (@lem5441324)). Qed.
Lemma lem5441326 : term759 = False.
Proof. exact (TRANS (@lem5441269) (@lem5441325)). Qed.
Lemma lem5441327 : term758 = False.
Proof. exact (TRANS (@lem5441260) (@lem5441326)). Qed.
Lemma lem5441328 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term562 _70504 _70506 _70505 _70507 _70508) : False.
Proof. exact (EQ_MP (@lem5441327) (@lem5441257 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5441329 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term569 _70504 _70506 _70505 _70507 _70508) : term569 _70504 _70506 _70505 _70507 _70508.
Proof. exact (h1). Qed.
Lemma lem5441330 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term569 _70504 _70506 _70505 _70507 _70508) : term567 _70504 _70506 _70505 _70507 _70508.
Proof. exact (proj2 (@lem5441329 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5441332 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term569 _70504 _70506 _70505 _70507 _70508) : term566 _70504 _70506 _70505 _70507 _70508.
Proof. exact (proj2 (@lem5441330 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5441334 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term569 _70504 _70506 _70505 _70507 _70508) : term565 _70504 _70506 _70505 _70507 _70508.
Proof. exact (proj2 (@lem5441332 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5441336 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term569 _70504 _70506 _70505 _70507 _70508) : term564 _70504 _70506 _70505 _70507 _70508.
Proof. exact (proj2 (@lem5441334 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5441338 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term569 _70504 _70506 _70505 _70507 _70508) : term563 _70504 _70506 _70505 _70507 _70508.
Proof. exact (proj2 (@lem5441336 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5441340 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term569 _70504 _70506 _70505 _70507 _70508) : term536 _70504 _70506 _70505 _70507 _70508.
Proof. exact (proj2 (@lem5441338 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5441341 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term569 _70504 _70506 _70505 _70507 _70508) : term338 _70507 _70508.
Proof. exact (proj1 (@lem5441338 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5441342 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term569 _70504 _70506 _70505 _70507 _70508) : term535 _70505 _70507 _70508.
Proof. exact (proj2 (@lem5441340 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5441346 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term569 _70504 _70506 _70505 _70507 _70508) : term368 _70507 _70508.
Proof. exact (proj2 (@lem5441342 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5441349 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5441350 : term699 = term700.
Proof. exact (@lem5441349 term214 term227). Qed.
Lemma lem5441352 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5441353 : term227 = term320.
Proof. exact (@lem5441352 term228). Qed.
Lemma lem5441355 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5441356 : term214 = term291.
Proof. exact (@lem5441355 (NUMERAL 0)). Qed.
Lemma lem5441357 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5441358 : term701 = term702.
Proof. exact (MK_COMB (@lem5441357) (@lem5441356)). Qed.
Lemma lem5441359 : term700 = term703.
Proof. exact (MK_COMB (@lem5441358) (@lem5441353)). Qed.
Lemma lem5441360 : term704.
Proof. exact (@lem1980255 term214 term227 term227 term227). Qed.
Lemma lem5441362 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441363 : term700 = term706.
Proof. exact (@lem5441362 (NUMERAL 0) term228). Qed.
Lemma lem5441364 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441365 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441366 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441365 h1) (fun h1 : term706 = True => @lem5441364)). Qed.
Lemma lem5441367 : term706 = True.
Proof. exact (EQ_MP (@lem5441366) (@lem5441364)). Qed.
Lemma lem5441368 : term700 = True.
Proof. exact (TRANS (@lem5441363) (@lem5441367)). Qed.
Lemma lem5441369 : True = term700.
Proof. exact (SYM (@lem5441368)). Qed.
Lemma lem5441370 : term700.
Proof. exact (EQ_MP (@lem5441369) (@lem0)). Qed.
Lemma lem5441371 : term708.
Proof. exact (@lem5441360 (@lem5441370)). Qed.
Lemma lem5441373 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441374 : term700 = term706.
Proof. exact (@lem5441373 (NUMERAL 0) term228). Qed.
Lemma lem5441375 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441376 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441377 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441376 h1) (fun h1 : term706 = True => @lem5441375)). Qed.
Lemma lem5441378 : term706 = True.
Proof. exact (EQ_MP (@lem5441377) (@lem5441375)). Qed.
Lemma lem5441379 : term700 = True.
Proof. exact (TRANS (@lem5441374) (@lem5441378)). Qed.
Lemma lem5441380 : True = term700.
Proof. exact (SYM (@lem5441379)). Qed.
Lemma lem5441381 : term700.
Proof. exact (EQ_MP (@lem5441380) (@lem0)). Qed.
Lemma lem5441382 : term703 = term709.
Proof. exact (@lem5441371 (@lem5441381)). Qed.
Lemma lem5441384 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5441385 : term303 = term304.
Proof. exact (@lem5441384 term228 term228). Qed.
Lemma lem5441386 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5441387 : term306 = term228.
Proof. exact (EQ_MP (@lem5441386) (@lem940073)). Qed.
Lemma lem5441388 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5441389 : term304 = term227.
Proof. exact (MK_COMB (@lem5441388) (@lem5441387)). Qed.
Lemma lem5441390 : term303 = term227.
Proof. exact (TRANS (@lem5441385) (@lem5441389)). Qed.
Lemma lem5441392 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5441393 : term711 = term214.
Proof. exact (@lem5441392 term228). Qed.
Lemma lem5441394 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5441395 : term712 = term701.
Proof. exact (MK_COMB (@lem5441394) (@lem5441393)). Qed.
Lemma lem5441396 : term709 = term700.
Proof. exact (MK_COMB (@lem5441395) (@lem5441390)). Qed.
Lemma lem5441398 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441399 : term700 = term706.
Proof. exact (@lem5441398 (NUMERAL 0) term228). Qed.
Lemma lem5441400 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441401 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441402 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441401 h1) (fun h1 : term706 = True => @lem5441400)). Qed.
Lemma lem5441403 : term706 = True.
Proof. exact (EQ_MP (@lem5441402) (@lem5441400)). Qed.
Lemma lem5441404 : term700 = True.
Proof. exact (TRANS (@lem5441399) (@lem5441403)). Qed.
Lemma lem5441405 : term709 = True.
Proof. exact (TRANS (@lem5441396) (@lem5441404)). Qed.
Lemma lem5441406 : term703 = True.
Proof. exact (TRANS (@lem5441382) (@lem5441405)). Qed.
Lemma lem5441407 : term700 = True.
Proof. exact (TRANS (@lem5441359) (@lem5441406)). Qed.
Lemma lem5441408 : term699 = True.
Proof. exact (TRANS (@lem5441350) (@lem5441407)). Qed.
Lemma lem5441409 : True = term699.
Proof. exact (SYM (@lem5441408)). Qed.
Lemma lem5441410 : term699.
Proof. exact (EQ_MP (@lem5441409) (@lem0)). Qed.
Lemma lem5441411 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term569 _70504 _70506 _70505 _70507 _70508) : term770 _70507 _70508.
Proof. exact (conj (@lem5441410) (@lem5441346 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5441413 (x : real) (y : real) : term714 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5441414 (_70507 : int) (_70508 : int) : term771 _70507 _70508.
Proof. exact (@lem5441413 term227 (term362 _70507 _70508)). Qed.
Lemma lem5441415 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term569 _70504 _70506 _70505 _70507 _70508) : term772 _70507 _70508.
Proof. exact (@lem5441414 _70507 _70508 (@lem5441411 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5441416 (_70507 : int) (_70508 : int) : (term773 _70507 _70508) = (term362 _70507 _70508).
Proof. exact (@lem1982733 (term362 _70507 _70508)). Qed.
Lemma lem5441417 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5441418 (_70507 : int) (_70508 : int) : (term774 _70507 _70508) = (term367 _70507 _70508).
Proof. exact (MK_COMB (@lem5441417) (@lem5441416 _70507 _70508)). Qed.
Lemma lem5441419 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5441420 (_70507 : int) (_70508 : int) : (term772 _70507 _70508) = (term368 _70507 _70508).
Proof. exact (MK_COMB (@lem5441418 _70507 _70508) (@lem5441419)). Qed.
Lemma lem5441421 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term569 _70504 _70506 _70505 _70507 _70508) : term368 _70507 _70508.
Proof. exact (EQ_MP (@lem5441420 _70507 _70508) (@lem5441415 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5441423 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5441424 : term699 = term700.
Proof. exact (@lem5441423 term214 term227). Qed.
Lemma lem5441426 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5441427 : term227 = term320.
Proof. exact (@lem5441426 term228). Qed.
Lemma lem5441429 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5441430 : term214 = term291.
Proof. exact (@lem5441429 (NUMERAL 0)). Qed.
Lemma lem5441431 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5441432 : term701 = term702.
Proof. exact (MK_COMB (@lem5441431) (@lem5441430)). Qed.
Lemma lem5441433 : term700 = term703.
Proof. exact (MK_COMB (@lem5441432) (@lem5441427)). Qed.
Lemma lem5441434 : term704.
Proof. exact (@lem1980255 term214 term227 term227 term227). Qed.
Lemma lem5441436 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441437 : term700 = term706.
Proof. exact (@lem5441436 (NUMERAL 0) term228). Qed.
Lemma lem5441438 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441439 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441440 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441439 h1) (fun h1 : term706 = True => @lem5441438)). Qed.
Lemma lem5441441 : term706 = True.
Proof. exact (EQ_MP (@lem5441440) (@lem5441438)). Qed.
Lemma lem5441442 : term700 = True.
Proof. exact (TRANS (@lem5441437) (@lem5441441)). Qed.
Lemma lem5441443 : True = term700.
Proof. exact (SYM (@lem5441442)). Qed.
Lemma lem5441444 : term700.
Proof. exact (EQ_MP (@lem5441443) (@lem0)). Qed.
Lemma lem5441445 : term708.
Proof. exact (@lem5441434 (@lem5441444)). Qed.
Lemma lem5441447 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441448 : term700 = term706.
Proof. exact (@lem5441447 (NUMERAL 0) term228). Qed.
Lemma lem5441449 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441450 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441451 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441450 h1) (fun h1 : term706 = True => @lem5441449)). Qed.
Lemma lem5441452 : term706 = True.
Proof. exact (EQ_MP (@lem5441451) (@lem5441449)). Qed.
Lemma lem5441453 : term700 = True.
Proof. exact (TRANS (@lem5441448) (@lem5441452)). Qed.
Lemma lem5441454 : True = term700.
Proof. exact (SYM (@lem5441453)). Qed.
Lemma lem5441455 : term700.
Proof. exact (EQ_MP (@lem5441454) (@lem0)). Qed.
Lemma lem5441456 : term703 = term709.
Proof. exact (@lem5441445 (@lem5441455)). Qed.
Lemma lem5441458 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5441459 : term303 = term304.
Proof. exact (@lem5441458 term228 term228). Qed.
Lemma lem5441460 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5441461 : term306 = term228.
Proof. exact (EQ_MP (@lem5441460) (@lem940073)). Qed.
Lemma lem5441462 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5441463 : term304 = term227.
Proof. exact (MK_COMB (@lem5441462) (@lem5441461)). Qed.
Lemma lem5441464 : term303 = term227.
Proof. exact (TRANS (@lem5441459) (@lem5441463)). Qed.
Lemma lem5441466 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5441467 : term711 = term214.
Proof. exact (@lem5441466 term228). Qed.
Lemma lem5441468 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5441469 : term712 = term701.
Proof. exact (MK_COMB (@lem5441468) (@lem5441467)). Qed.
Lemma lem5441470 : term709 = term700.
Proof. exact (MK_COMB (@lem5441469) (@lem5441464)). Qed.
Lemma lem5441472 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441473 : term700 = term706.
Proof. exact (@lem5441472 (NUMERAL 0) term228). Qed.
Lemma lem5441474 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441475 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441476 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441475 h1) (fun h1 : term706 = True => @lem5441474)). Qed.
Lemma lem5441477 : term706 = True.
Proof. exact (EQ_MP (@lem5441476) (@lem5441474)). Qed.
Lemma lem5441478 : term700 = True.
Proof. exact (TRANS (@lem5441473) (@lem5441477)). Qed.
Lemma lem5441479 : term709 = True.
Proof. exact (TRANS (@lem5441470) (@lem5441478)). Qed.
Lemma lem5441480 : term703 = True.
Proof. exact (TRANS (@lem5441456) (@lem5441479)). Qed.
Lemma lem5441481 : term700 = True.
Proof. exact (TRANS (@lem5441433) (@lem5441480)). Qed.
Lemma lem5441482 : term699 = True.
Proof. exact (TRANS (@lem5441424) (@lem5441481)). Qed.
Lemma lem5441483 : True = term699.
Proof. exact (SYM (@lem5441482)). Qed.
Lemma lem5441484 : term699.
Proof. exact (EQ_MP (@lem5441483) (@lem0)). Qed.
Lemma lem5441485 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term569 _70504 _70506 _70505 _70507 _70508) : term775 _70507 _70508.
Proof. exact (conj (@lem5441484) (@lem5441341 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5441487 (x : real) (y : real) : term714 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5441488 (_70507 : int) (_70508 : int) : term776 _70507 _70508.
Proof. exact (@lem5441487 term227 (term335 _70507 _70508)). Qed.
Lemma lem5441489 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term569 _70504 _70506 _70505 _70507 _70508) : term777 _70507 _70508.
Proof. exact (@lem5441488 _70507 _70508 (@lem5441485 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5441490 (_70507 : int) (_70508 : int) : (term778 _70507 _70508) = (term335 _70507 _70508).
Proof. exact (@lem1982733 (term335 _70507 _70508)). Qed.
Lemma lem5441491 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5441492 (_70507 : int) (_70508 : int) : (term779 _70507 _70508) = (term337 _70507 _70508).
Proof. exact (MK_COMB (@lem5441491) (@lem5441490 _70507 _70508)). Qed.
Lemma lem5441493 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5441494 (_70507 : int) (_70508 : int) : (term777 _70507 _70508) = (term338 _70507 _70508).
Proof. exact (MK_COMB (@lem5441492 _70507 _70508) (@lem5441493)). Qed.
Lemma lem5441495 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term569 _70504 _70506 _70505 _70507 _70508) : term338 _70507 _70508.
Proof. exact (EQ_MP (@lem5441494 _70507 _70508) (@lem5441489 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5441496 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term569 _70504 _70506 _70505 _70507 _70508) : term780 _70507 _70508.
Proof. exact (conj (@lem5441495 _70504 _70506 _70505 _70507 _70508 h1) (@lem5441421 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5441498 (x : real) (y : real) : term725 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5441499 (_70507 : int) (_70508 : int) : term781 _70507 _70508.
Proof. exact (@lem5441498 (term335 _70507 _70508) (term362 _70507 _70508)). Qed.
Lemma lem5441500 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term569 _70504 _70506 _70505 _70507 _70508) : term782 _70507 _70508.
Proof. exact (@lem5441499 _70507 _70508 (@lem5441496 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5441501 (_70507 : int) (_70508 : int) : (term783 _70507 _70508) = (term784 _70507 _70508).
Proof. exact (@lem1982753 (term336 _70507) (real_of_int _70507) (term785 _70508) (term336 _70508)). Qed.
Lemma lem5441502 (_70507 : int) : (term730 _70507) = (term731 _70507).
Proof. exact (@lem1982713 term294 (real_of_int _70507)). Qed.
Lemma lem5441504 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5441505 : term227 = term320.
Proof. exact (@lem5441504 term228). Qed.
Lemma lem5441507 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5441508 : term294 = term295.
Proof. exact (@lem5441507 term228). Qed.
Lemma lem5441509 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5441510 : term732 = term733.
Proof. exact (MK_COMB (@lem5441509) (@lem5441508)). Qed.
Lemma lem5441511 : term734 = term735.
Proof. exact (MK_COMB (@lem5441510) (@lem5441505)). Qed.
Lemma lem5441512 : term736.
Proof. exact (@lem1981473 term294 term227 term227 term227 term214 term227). Qed.
Lemma lem5441514 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441515 : term700 = term706.
Proof. exact (@lem5441514 (NUMERAL 0) term228). Qed.
Lemma lem5441516 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441517 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441518 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441517 h1) (fun h1 : term706 = True => @lem5441516)). Qed.
Lemma lem5441519 : term706 = True.
Proof. exact (EQ_MP (@lem5441518) (@lem5441516)). Qed.
Lemma lem5441520 : term700 = True.
Proof. exact (TRANS (@lem5441515) (@lem5441519)). Qed.
Lemma lem5441521 : True = term700.
Proof. exact (SYM (@lem5441520)). Qed.
Lemma lem5441522 : term700.
Proof. exact (EQ_MP (@lem5441521) (@lem0)). Qed.
Lemma lem5441523 : term737.
Proof. exact (@lem5441512 (@lem5441522)). Qed.
Lemma lem5441525 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441526 : term700 = term706.
Proof. exact (@lem5441525 (NUMERAL 0) term228). Qed.
Lemma lem5441527 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441528 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441529 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441528 h1) (fun h1 : term706 = True => @lem5441527)). Qed.
Lemma lem5441530 : term706 = True.
Proof. exact (EQ_MP (@lem5441529) (@lem5441527)). Qed.
Lemma lem5441531 : term700 = True.
Proof. exact (TRANS (@lem5441526) (@lem5441530)). Qed.
Lemma lem5441532 : True = term700.
Proof. exact (SYM (@lem5441531)). Qed.
Lemma lem5441533 : term700.
Proof. exact (EQ_MP (@lem5441532) (@lem0)). Qed.
Lemma lem5441534 : term738.
Proof. exact (@lem5441523 (@lem5441533)). Qed.
Lemma lem5441536 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441537 : term700 = term706.
Proof. exact (@lem5441536 (NUMERAL 0) term228). Qed.
Lemma lem5441538 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441539 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441540 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441539 h1) (fun h1 : term706 = True => @lem5441538)). Qed.
Lemma lem5441541 : term706 = True.
Proof. exact (EQ_MP (@lem5441540) (@lem5441538)). Qed.
Lemma lem5441542 : term700 = True.
Proof. exact (TRANS (@lem5441537) (@lem5441541)). Qed.
Lemma lem5441543 : True = term700.
Proof. exact (SYM (@lem5441542)). Qed.
Lemma lem5441544 : term700.
Proof. exact (EQ_MP (@lem5441543) (@lem0)). Qed.
Lemma lem5441545 : term739.
Proof. exact (@lem5441534 (@lem5441544)). Qed.
Lemma lem5441547 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5441548 : term303 = term304.
Proof. exact (@lem5441547 term228 term228). Qed.
Lemma lem5441549 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5441550 : term306 = term228.
Proof. exact (EQ_MP (@lem5441549) (@lem940073)). Qed.
Lemma lem5441551 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5441552 : term304 = term227.
Proof. exact (MK_COMB (@lem5441551) (@lem5441550)). Qed.
Lemma lem5441553 : term303 = term227.
Proof. exact (TRANS (@lem5441548) (@lem5441552)). Qed.
Lemma lem5441555 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5441556 : term321 = term326.
Proof. exact (@lem5441555 term228 term228). Qed.
Lemma lem5441557 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5441558 : term306 = term228.
Proof. exact (EQ_MP (@lem5441557) (@lem940073)). Qed.
Lemma lem5441559 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5441560 : term304 = term227.
Proof. exact (MK_COMB (@lem5441559) (@lem5441558)). Qed.
Lemma lem5441561 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5441562 : term326 = term294.
Proof. exact (MK_COMB (@lem5441561) (@lem5441560)). Qed.
Lemma lem5441563 : term321 = term294.
Proof. exact (TRANS (@lem5441556) (@lem5441562)). Qed.
Lemma lem5441564 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5441565 : term740 = term732.
Proof. exact (MK_COMB (@lem5441564) (@lem5441563)). Qed.
Lemma lem5441566 : term741 = term734.
Proof. exact (MK_COMB (@lem5441565) (@lem5441553)). Qed.
Lemma lem5441568 (m : nat) : (term742 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5441569 : term734 = term214.
Proof. exact (@lem5441568 term228). Qed.
Lemma lem5441570 : term741 = term214.
Proof. exact (TRANS (@lem5441566) (@lem5441569)). Qed.
Lemma lem5441571 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5441572 : term743 = term744.
Proof. exact (MK_COMB (@lem5441571) (@lem5441570)). Qed.
Lemma lem5441573 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem5441574 : term745 = term711.
Proof. exact (MK_COMB (@lem5441572) (@lem5441573)). Qed.
Lemma lem5441576 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5441577 : term711 = term214.
Proof. exact (@lem5441576 term228). Qed.
Lemma lem5441578 : term745 = term214.
Proof. exact (TRANS (@lem5441574) (@lem5441577)). Qed.
Lemma lem5441580 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5441581 : term303 = term304.
Proof. exact (@lem5441580 term228 term228). Qed.
Lemma lem5441582 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5441583 : term306 = term228.
Proof. exact (EQ_MP (@lem5441582) (@lem940073)). Qed.
Lemma lem5441584 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5441585 : term304 = term227.
Proof. exact (MK_COMB (@lem5441584) (@lem5441583)). Qed.
Lemma lem5441586 : term303 = term227.
Proof. exact (TRANS (@lem5441581) (@lem5441585)). Qed.
Lemma lem5441587 : term744 = term744.
Proof. exact (eq_refl term744). Qed.
Lemma lem5441588 : term746 = term711.
Proof. exact (MK_COMB (@lem5441587) (@lem5441586)). Qed.
Lemma lem5441590 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5441591 : term711 = term214.
Proof. exact (@lem5441590 term228). Qed.
Lemma lem5441592 : term746 = term214.
Proof. exact (TRANS (@lem5441588) (@lem5441591)). Qed.
Lemma lem5441593 : term214 = term746.
Proof. exact (SYM (@lem5441592)). Qed.
Lemma lem5441594 : term745 = term746.
Proof. exact (TRANS (@lem5441578) (@lem5441593)). Qed.
Lemma lem5441595 : term735 = term291.
Proof. exact (@lem5441545 (@lem5441594)). Qed.
Lemma lem5441596 : term734 = term291.
Proof. exact (TRANS (@lem5441511) (@lem5441595)). Qed.
Lemma lem5441598 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5441599 : term291 = term214.
Proof. exact (@lem5441598 term214). Qed.
Lemma lem5441600 : term734 = term214.
Proof. exact (TRANS (@lem5441596) (@lem5441599)). Qed.
Lemma lem5441601 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5441602 : term747 = term744.
Proof. exact (MK_COMB (@lem5441601) (@lem5441600)). Qed.
Lemma lem5441603 (_70507 : int) : (real_of_int _70507) = (real_of_int _70507).
Proof. exact (eq_refl (real_of_int _70507)). Qed.
Lemma lem5441604 (_70507 : int) : (term731 _70507) = (term748 _70507).
Proof. exact (MK_COMB (@lem5441602) (@lem5441603 _70507)). Qed.
Lemma lem5441605 (_70507 : int) : (term730 _70507) = (term748 _70507).
Proof. exact (TRANS (@lem5441502 _70507) (@lem5441604 _70507)). Qed.
Lemma lem5441606 (_70507 : int) : (term748 _70507) = term214.
Proof. exact (@lem1982719 (real_of_int _70507)). Qed.
Lemma lem5441607 (_70507 : int) : (term730 _70507) = term214.
Proof. exact (TRANS (@lem5441605 _70507) (@lem5441606 _70507)). Qed.
Lemma lem5441608 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5441609 (_70507 : int) : (term749 _70507) = term750.
Proof. exact (MK_COMB (@lem5441608) (@lem5441607 _70507)). Qed.
Lemma lem5441610 (_70508 : int) : (term786 _70508) = (term752 _70508).
Proof. exact (@lem1982759 (real_of_int _70508) (term336 _70508) term294). Qed.
Lemma lem5441611 (_70508 : int) : (term753 _70508) = (term731 _70508).
Proof. exact (@lem1982715 term294 (real_of_int _70508)). Qed.
Lemma lem5441613 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5441614 : term227 = term320.
Proof. exact (@lem5441613 term228). Qed.
Lemma lem5441616 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5441617 : term294 = term295.
Proof. exact (@lem5441616 term228). Qed.
Lemma lem5441618 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5441619 : term732 = term733.
Proof. exact (MK_COMB (@lem5441618) (@lem5441617)). Qed.
Lemma lem5441620 : term734 = term735.
Proof. exact (MK_COMB (@lem5441619) (@lem5441614)). Qed.
Lemma lem5441621 : term736.
Proof. exact (@lem1981473 term294 term227 term227 term227 term214 term227). Qed.
Lemma lem5441623 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441624 : term700 = term706.
Proof. exact (@lem5441623 (NUMERAL 0) term228). Qed.
Lemma lem5441625 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441626 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441627 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441626 h1) (fun h1 : term706 = True => @lem5441625)). Qed.
Lemma lem5441628 : term706 = True.
Proof. exact (EQ_MP (@lem5441627) (@lem5441625)). Qed.
Lemma lem5441629 : term700 = True.
Proof. exact (TRANS (@lem5441624) (@lem5441628)). Qed.
Lemma lem5441630 : True = term700.
Proof. exact (SYM (@lem5441629)). Qed.
Lemma lem5441631 : term700.
Proof. exact (EQ_MP (@lem5441630) (@lem0)). Qed.
Lemma lem5441632 : term737.
Proof. exact (@lem5441621 (@lem5441631)). Qed.
Lemma lem5441634 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441635 : term700 = term706.
Proof. exact (@lem5441634 (NUMERAL 0) term228). Qed.
Lemma lem5441636 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441637 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441638 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441637 h1) (fun h1 : term706 = True => @lem5441636)). Qed.
Lemma lem5441639 : term706 = True.
Proof. exact (EQ_MP (@lem5441638) (@lem5441636)). Qed.
Lemma lem5441640 : term700 = True.
Proof. exact (TRANS (@lem5441635) (@lem5441639)). Qed.
Lemma lem5441641 : True = term700.
Proof. exact (SYM (@lem5441640)). Qed.
Lemma lem5441642 : term700.
Proof. exact (EQ_MP (@lem5441641) (@lem0)). Qed.
Lemma lem5441643 : term738.
Proof. exact (@lem5441632 (@lem5441642)). Qed.
Lemma lem5441645 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441646 : term700 = term706.
Proof. exact (@lem5441645 (NUMERAL 0) term228). Qed.
Lemma lem5441647 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441648 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441649 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441648 h1) (fun h1 : term706 = True => @lem5441647)). Qed.
Lemma lem5441650 : term706 = True.
Proof. exact (EQ_MP (@lem5441649) (@lem5441647)). Qed.
Lemma lem5441651 : term700 = True.
Proof. exact (TRANS (@lem5441646) (@lem5441650)). Qed.
Lemma lem5441652 : True = term700.
Proof. exact (SYM (@lem5441651)). Qed.
Lemma lem5441653 : term700.
Proof. exact (EQ_MP (@lem5441652) (@lem0)). Qed.
Lemma lem5441654 : term739.
Proof. exact (@lem5441643 (@lem5441653)). Qed.
Lemma lem5441656 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5441657 : term303 = term304.
Proof. exact (@lem5441656 term228 term228). Qed.
Lemma lem5441658 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5441659 : term306 = term228.
Proof. exact (EQ_MP (@lem5441658) (@lem940073)). Qed.
Lemma lem5441660 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5441661 : term304 = term227.
Proof. exact (MK_COMB (@lem5441660) (@lem5441659)). Qed.
Lemma lem5441662 : term303 = term227.
Proof. exact (TRANS (@lem5441657) (@lem5441661)). Qed.
Lemma lem5441664 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5441665 : term321 = term326.
Proof. exact (@lem5441664 term228 term228). Qed.
Lemma lem5441666 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5441667 : term306 = term228.
Proof. exact (EQ_MP (@lem5441666) (@lem940073)). Qed.
Lemma lem5441668 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5441669 : term304 = term227.
Proof. exact (MK_COMB (@lem5441668) (@lem5441667)). Qed.
Lemma lem5441670 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5441671 : term326 = term294.
Proof. exact (MK_COMB (@lem5441670) (@lem5441669)). Qed.
Lemma lem5441672 : term321 = term294.
Proof. exact (TRANS (@lem5441665) (@lem5441671)). Qed.
Lemma lem5441673 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5441674 : term740 = term732.
Proof. exact (MK_COMB (@lem5441673) (@lem5441672)). Qed.
Lemma lem5441675 : term741 = term734.
Proof. exact (MK_COMB (@lem5441674) (@lem5441662)). Qed.
Lemma lem5441677 (m : nat) : (term742 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5441678 : term734 = term214.
Proof. exact (@lem5441677 term228). Qed.
Lemma lem5441679 : term741 = term214.
Proof. exact (TRANS (@lem5441675) (@lem5441678)). Qed.
Lemma lem5441680 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5441681 : term743 = term744.
Proof. exact (MK_COMB (@lem5441680) (@lem5441679)). Qed.
Lemma lem5441682 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem5441683 : term745 = term711.
Proof. exact (MK_COMB (@lem5441681) (@lem5441682)). Qed.
Lemma lem5441685 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5441686 : term711 = term214.
Proof. exact (@lem5441685 term228). Qed.
Lemma lem5441687 : term745 = term214.
Proof. exact (TRANS (@lem5441683) (@lem5441686)). Qed.
Lemma lem5441689 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5441690 : term303 = term304.
Proof. exact (@lem5441689 term228 term228). Qed.
Lemma lem5441691 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5441692 : term306 = term228.
Proof. exact (EQ_MP (@lem5441691) (@lem940073)). Qed.
Lemma lem5441693 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5441694 : term304 = term227.
Proof. exact (MK_COMB (@lem5441693) (@lem5441692)). Qed.
Lemma lem5441695 : term303 = term227.
Proof. exact (TRANS (@lem5441690) (@lem5441694)). Qed.
Lemma lem5441696 : term744 = term744.
Proof. exact (eq_refl term744). Qed.
Lemma lem5441697 : term746 = term711.
Proof. exact (MK_COMB (@lem5441696) (@lem5441695)). Qed.
Lemma lem5441699 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5441700 : term711 = term214.
Proof. exact (@lem5441699 term228). Qed.
Lemma lem5441701 : term746 = term214.
Proof. exact (TRANS (@lem5441697) (@lem5441700)). Qed.
Lemma lem5441702 : term214 = term746.
Proof. exact (SYM (@lem5441701)). Qed.
Lemma lem5441703 : term745 = term746.
Proof. exact (TRANS (@lem5441687) (@lem5441702)). Qed.
Lemma lem5441704 : term735 = term291.
Proof. exact (@lem5441654 (@lem5441703)). Qed.
Lemma lem5441705 : term734 = term291.
Proof. exact (TRANS (@lem5441620) (@lem5441704)). Qed.
Lemma lem5441707 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5441708 : term291 = term214.
Proof. exact (@lem5441707 term214). Qed.
Lemma lem5441709 : term734 = term214.
Proof. exact (TRANS (@lem5441705) (@lem5441708)). Qed.
Lemma lem5441710 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5441711 : term747 = term744.
Proof. exact (MK_COMB (@lem5441710) (@lem5441709)). Qed.
Lemma lem5441712 (_70508 : int) : (real_of_int _70508) = (real_of_int _70508).
Proof. exact (eq_refl (real_of_int _70508)). Qed.
Lemma lem5441713 (_70508 : int) : (term731 _70508) = (term748 _70508).
Proof. exact (MK_COMB (@lem5441711) (@lem5441712 _70508)). Qed.
Lemma lem5441714 (_70508 : int) : (term753 _70508) = (term748 _70508).
Proof. exact (TRANS (@lem5441611 _70508) (@lem5441713 _70508)). Qed.
Lemma lem5441715 (_70508 : int) : (term748 _70508) = term214.
Proof. exact (@lem1982719 (real_of_int _70508)). Qed.
Lemma lem5441716 (_70508 : int) : (term753 _70508) = term214.
Proof. exact (TRANS (@lem5441714 _70508) (@lem5441715 _70508)). Qed.
Lemma lem5441717 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5441718 (_70508 : int) : (term754 _70508) = term750.
Proof. exact (MK_COMB (@lem5441717) (@lem5441716 _70508)). Qed.
Lemma lem5441719 : term294 = term294.
Proof. exact (eq_refl term294). Qed.
Lemma lem5441720 (_70508 : int) : (term752 _70508) = term755.
Proof. exact (MK_COMB (@lem5441718 _70508) (@lem5441719)). Qed.
Lemma lem5441721 (_70508 : int) : (term786 _70508) = term755.
Proof. exact (TRANS (@lem5441610 _70508) (@lem5441720 _70508)). Qed.
Lemma lem5441722 : term755 = term294.
Proof. exact (@lem1982721 term294). Qed.
Lemma lem5441723 (_70508 : int) : (term786 _70508) = term294.
Proof. exact (TRANS (@lem5441721 _70508) (@lem5441722)). Qed.
Lemma lem5441724 (_70507 : int) (_70508 : int) : (term784 _70507 _70508) = term755.
Proof. exact (MK_COMB (@lem5441609 _70507) (@lem5441723 _70508)). Qed.
Lemma lem5441725 (_70507 : int) (_70508 : int) : (term783 _70507 _70508) = term755.
Proof. exact (TRANS (@lem5441501 _70507 _70508) (@lem5441724 _70507 _70508)). Qed.
Lemma lem5441726 : term755 = term294.
Proof. exact (@lem1982721 term294). Qed.
Lemma lem5441727 (_70507 : int) (_70508 : int) : (term783 _70507 _70508) = term294.
Proof. exact (TRANS (@lem5441725 _70507 _70508) (@lem5441726)). Qed.
Lemma lem5441728 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5441729 (_70507 : int) (_70508 : int) : (term787 _70507 _70508) = term757.
Proof. exact (MK_COMB (@lem5441728) (@lem5441727 _70507 _70508)). Qed.
Lemma lem5441730 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5441731 (_70507 : int) (_70508 : int) : (term782 _70507 _70508) = term758.
Proof. exact (MK_COMB (@lem5441729 _70507 _70508) (@lem5441730)). Qed.
Lemma lem5441732 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term569 _70504 _70506 _70505 _70507 _70508) : term758.
Proof. exact (EQ_MP (@lem5441731 _70507 _70508) (@lem5441500 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5441734 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5441735 : term758 = term759.
Proof. exact (@lem5441734 term214 term294). Qed.
Lemma lem5441737 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5441738 : term294 = term295.
Proof. exact (@lem5441737 term228). Qed.
Lemma lem5441740 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5441741 : term214 = term291.
Proof. exact (@lem5441740 (NUMERAL 0)). Qed.
Lemma lem5441742 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5441743 : term216 = term760.
Proof. exact (MK_COMB (@lem5441742) (@lem5441741)). Qed.
Lemma lem5441744 : term759 = term761.
Proof. exact (MK_COMB (@lem5441743) (@lem5441738)). Qed.
Lemma lem5441745 : term762.
Proof. exact (@lem1980026 term214 term227 term294 term227). Qed.
Lemma lem5441747 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441748 : term700 = term706.
Proof. exact (@lem5441747 (NUMERAL 0) term228). Qed.
Lemma lem5441749 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441750 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441751 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441750 h1) (fun h1 : term706 = True => @lem5441749)). Qed.
Lemma lem5441752 : term706 = True.
Proof. exact (EQ_MP (@lem5441751) (@lem5441749)). Qed.
Lemma lem5441753 : term700 = True.
Proof. exact (TRANS (@lem5441748) (@lem5441752)). Qed.
Lemma lem5441754 : True = term700.
Proof. exact (SYM (@lem5441753)). Qed.
Lemma lem5441755 : term700.
Proof. exact (EQ_MP (@lem5441754) (@lem0)). Qed.
Lemma lem5441756 : term763.
Proof. exact (@lem5441745 (@lem5441755)). Qed.
Lemma lem5441758 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441759 : term700 = term706.
Proof. exact (@lem5441758 (NUMERAL 0) term228). Qed.
Lemma lem5441760 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441761 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441762 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441761 h1) (fun h1 : term706 = True => @lem5441760)). Qed.
Lemma lem5441763 : term706 = True.
Proof. exact (EQ_MP (@lem5441762) (@lem5441760)). Qed.
Lemma lem5441764 : term700 = True.
Proof. exact (TRANS (@lem5441759) (@lem5441763)). Qed.
Lemma lem5441765 : True = term700.
Proof. exact (SYM (@lem5441764)). Qed.
Lemma lem5441766 : term700.
Proof. exact (EQ_MP (@lem5441765) (@lem0)). Qed.
Lemma lem5441767 : term761 = term764.
Proof. exact (@lem5441756 (@lem5441766)). Qed.
Lemma lem5441769 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5441770 : term321 = term326.
Proof. exact (@lem5441769 term228 term228). Qed.
Lemma lem5441771 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5441772 : term306 = term228.
Proof. exact (EQ_MP (@lem5441771) (@lem940073)). Qed.
Lemma lem5441773 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5441774 : term304 = term227.
Proof. exact (MK_COMB (@lem5441773) (@lem5441772)). Qed.
Lemma lem5441775 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5441776 : term326 = term294.
Proof. exact (MK_COMB (@lem5441775) (@lem5441774)). Qed.
Lemma lem5441777 : term321 = term294.
Proof. exact (TRANS (@lem5441770) (@lem5441776)). Qed.
Lemma lem5441779 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5441780 : term711 = term214.
Proof. exact (@lem5441779 term228). Qed.
Lemma lem5441781 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5441782 : term765 = term216.
Proof. exact (MK_COMB (@lem5441781) (@lem5441780)). Qed.
Lemma lem5441783 : term764 = term759.
Proof. exact (MK_COMB (@lem5441782) (@lem5441777)). Qed.
Lemma lem5441785 (m : nat) (n : nat) : (term766 m n) = (term767 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5441786 : term759 = term768.
Proof. exact (@lem5441785 (NUMERAL 0) term228). Qed.
Lemma lem5441787 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441788 (h1 : term707 = (BIT1 0)) : (term228 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5441789 : (term707 = (BIT1 0)) = ((term228 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441788 h1) (fun h1 : (term228 = (NUMERAL 0)) = False => @lem5441787)). Qed.
Lemma lem5441790 : (term228 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5441789) (@lem5441787)). Qed.
Lemma lem5441791 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5441792 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5441793 : term769 = (and True).
Proof. exact (MK_COMB (@lem5441792) (@lem5441791)). Qed.
Lemma lem5441794 : term768 = (True /\ False).
Proof. exact (MK_COMB (@lem5441793) (@lem5441790)). Qed.
Lemma lem5441796 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5441797 : term768 = False.
Proof. exact (TRANS (@lem5441794) (@lem5441796)). Qed.
Lemma lem5441798 : term759 = False.
Proof. exact (TRANS (@lem5441786) (@lem5441797)). Qed.
Lemma lem5441799 : term764 = False.
Proof. exact (TRANS (@lem5441783) (@lem5441798)). Qed.
Lemma lem5441800 : term761 = False.
Proof. exact (TRANS (@lem5441767) (@lem5441799)). Qed.
Lemma lem5441801 : term759 = False.
Proof. exact (TRANS (@lem5441744) (@lem5441800)). Qed.
Lemma lem5441802 : term758 = False.
Proof. exact (TRANS (@lem5441735) (@lem5441801)). Qed.
Lemma lem5441803 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term569 _70504 _70506 _70505 _70507 _70508) : False.
Proof. exact (EQ_MP (@lem5441802) (@lem5441732 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5441804 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term572 _70504 _70506 _70505 _70507 _70508) : False.
Proof. exact (or_elim (@lem5440853 _70504 _70506 _70505 _70507 _70508 h1) (fun h0 : term562 _70504 _70506 _70505 _70507 _70508 => @lem5441328 _70504 _70506 _70505 _70507 _70508 h0) (fun h0 : term569 _70504 _70506 _70505 _70507 _70508 => @lem5441803 _70504 _70506 _70505 _70507 _70508 h0)). Qed.
Lemma lem5441805 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term574 _70504 _70506 _70505 _70507 _70508) : False.
Proof. exact (or_elim (@lem5439900 _70504 _70506 _70505 _70507 _70508 h1) (fun h0 : term555 _70504 _70506 _70505 _70507 _70508 => @lem5440852 _70504 _70506 _70505 _70507 _70508 h0) (fun h0 : term572 _70504 _70506 _70505 _70507 _70508 => @lem5441804 _70504 _70506 _70505 _70507 _70508 h0)). Qed.
Lemma lem5441806 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term696 _70504 _70505 _70506 _70507 _70508) : term696 _70504 _70505 _70506 _70507 _70508.
Proof. exact (h1). Qed.
Lemma lem5441807 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) (h1 : term646 _70505 _70506 _70507 _70504 _70508) : term646 _70505 _70506 _70507 _70504 _70508.
Proof. exact (h1). Qed.
Lemma lem5441808 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) (h1 : term626 _70504 _70505 _70507 _70506 _70508) : term626 _70504 _70505 _70507 _70506 _70508.
Proof. exact (h1). Qed.
Lemma lem5441809 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) (h1 : term626 _70504 _70505 _70507 _70506 _70508) : term625 _70504 _70505 _70507 _70506 _70508.
Proof. exact (proj2 (@lem5441808 _70504 _70505 _70507 _70506 _70508 h1)). Qed.
Lemma lem5441811 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) (h1 : term626 _70504 _70505 _70507 _70506 _70508) : term624 _70504 _70505 _70507 _70506 _70508.
Proof. exact (proj2 (@lem5441809 _70504 _70505 _70507 _70506 _70508 h1)). Qed.
Lemma lem5441813 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) (h1 : term626 _70504 _70505 _70507 _70506 _70508) : term622 _70504 _70505 _70507 _70506 _70508.
Proof. exact (proj2 (@lem5441811 _70504 _70505 _70507 _70506 _70508 h1)). Qed.
Lemma lem5441815 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) (h1 : term626 _70504 _70505 _70507 _70506 _70508) : term620 _70504 _70505 _70507 _70506 _70508.
Proof. exact (proj2 (@lem5441813 _70504 _70505 _70507 _70506 _70508 h1)). Qed.
Lemma lem5441817 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) (h1 : term626 _70504 _70505 _70507 _70506 _70508) : term618 _70504 _70505 _70507 _70506 _70508.
Proof. exact (proj2 (@lem5441815 _70504 _70505 _70507 _70506 _70508 h1)). Qed.
Lemma lem5441819 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) (h1 : term626 _70504 _70505 _70507 _70506 _70508) : term616 _70504 _70505 _70507 _70506 _70508.
Proof. exact (proj2 (@lem5441817 _70504 _70505 _70507 _70506 _70508 h1)). Qed.
Lemma lem5441821 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) (h1 : term626 _70504 _70505 _70507 _70506 _70508) : term334 _70506 _70508.
Proof. exact (proj2 (@lem5441819 _70504 _70505 _70507 _70506 _70508 h1)). Qed.
Lemma lem5441822 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) (h1 : term626 _70504 _70505 _70507 _70506 _70508) : term372 _70504 _70505 _70506 _70507 _70508.
Proof. exact (proj1 (@lem5441819 _70504 _70505 _70507 _70506 _70508 h1)). Qed.
Lemma lem5441823 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) (h1 : term626 _70504 _70505 _70507 _70506 _70508) : term370 _70506 _70507 _70508.
Proof. exact (proj2 (@lem5441822 _70504 _70505 _70507 _70506 _70508 h1)). Qed.
Lemma lem5441828 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) (h1 : term626 _70504 _70505 _70507 _70506 _70508) : term366 _70506 _70508.
Proof. exact (proj1 (@lem5441823 _70504 _70505 _70507 _70506 _70508 h1)). Qed.
Lemma lem5441830 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5441831 : term699 = term700.
Proof. exact (@lem5441830 term214 term227). Qed.
Lemma lem5441833 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5441834 : term227 = term320.
Proof. exact (@lem5441833 term228). Qed.
Lemma lem5441836 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5441837 : term214 = term291.
Proof. exact (@lem5441836 (NUMERAL 0)). Qed.
Lemma lem5441838 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5441839 : term701 = term702.
Proof. exact (MK_COMB (@lem5441838) (@lem5441837)). Qed.
Lemma lem5441840 : term700 = term703.
Proof. exact (MK_COMB (@lem5441839) (@lem5441834)). Qed.
Lemma lem5441841 : term704.
Proof. exact (@lem1980255 term214 term227 term227 term227). Qed.
Lemma lem5441843 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441844 : term700 = term706.
Proof. exact (@lem5441843 (NUMERAL 0) term228). Qed.
Lemma lem5441845 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441846 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441847 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441846 h1) (fun h1 : term706 = True => @lem5441845)). Qed.
Lemma lem5441848 : term706 = True.
Proof. exact (EQ_MP (@lem5441847) (@lem5441845)). Qed.
Lemma lem5441849 : term700 = True.
Proof. exact (TRANS (@lem5441844) (@lem5441848)). Qed.
Lemma lem5441850 : True = term700.
Proof. exact (SYM (@lem5441849)). Qed.
Lemma lem5441851 : term700.
Proof. exact (EQ_MP (@lem5441850) (@lem0)). Qed.
Lemma lem5441852 : term708.
Proof. exact (@lem5441841 (@lem5441851)). Qed.
Lemma lem5441854 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441855 : term700 = term706.
Proof. exact (@lem5441854 (NUMERAL 0) term228). Qed.
Lemma lem5441856 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441857 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441858 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441857 h1) (fun h1 : term706 = True => @lem5441856)). Qed.
Lemma lem5441859 : term706 = True.
Proof. exact (EQ_MP (@lem5441858) (@lem5441856)). Qed.
Lemma lem5441860 : term700 = True.
Proof. exact (TRANS (@lem5441855) (@lem5441859)). Qed.
Lemma lem5441861 : True = term700.
Proof. exact (SYM (@lem5441860)). Qed.
Lemma lem5441862 : term700.
Proof. exact (EQ_MP (@lem5441861) (@lem0)). Qed.
Lemma lem5441863 : term703 = term709.
Proof. exact (@lem5441852 (@lem5441862)). Qed.
Lemma lem5441865 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5441866 : term303 = term304.
Proof. exact (@lem5441865 term228 term228). Qed.
Lemma lem5441867 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5441868 : term306 = term228.
Proof. exact (EQ_MP (@lem5441867) (@lem940073)). Qed.
Lemma lem5441869 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5441870 : term304 = term227.
Proof. exact (MK_COMB (@lem5441869) (@lem5441868)). Qed.
Lemma lem5441871 : term303 = term227.
Proof. exact (TRANS (@lem5441866) (@lem5441870)). Qed.
Lemma lem5441873 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5441874 : term711 = term214.
Proof. exact (@lem5441873 term228). Qed.
Lemma lem5441875 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5441876 : term712 = term701.
Proof. exact (MK_COMB (@lem5441875) (@lem5441874)). Qed.
Lemma lem5441877 : term709 = term700.
Proof. exact (MK_COMB (@lem5441876) (@lem5441871)). Qed.
Lemma lem5441879 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441880 : term700 = term706.
Proof. exact (@lem5441879 (NUMERAL 0) term228). Qed.
Lemma lem5441881 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441882 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441883 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441882 h1) (fun h1 : term706 = True => @lem5441881)). Qed.
Lemma lem5441884 : term706 = True.
Proof. exact (EQ_MP (@lem5441883) (@lem5441881)). Qed.
Lemma lem5441885 : term700 = True.
Proof. exact (TRANS (@lem5441880) (@lem5441884)). Qed.
Lemma lem5441886 : term709 = True.
Proof. exact (TRANS (@lem5441877) (@lem5441885)). Qed.
Lemma lem5441887 : term703 = True.
Proof. exact (TRANS (@lem5441863) (@lem5441886)). Qed.
Lemma lem5441888 : term700 = True.
Proof. exact (TRANS (@lem5441840) (@lem5441887)). Qed.
Lemma lem5441889 : term699 = True.
Proof. exact (TRANS (@lem5441831) (@lem5441888)). Qed.
Lemma lem5441890 : True = term699.
Proof. exact (SYM (@lem5441889)). Qed.
Lemma lem5441891 : term699.
Proof. exact (EQ_MP (@lem5441890) (@lem0)). Qed.
Lemma lem5441892 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) (h1 : term626 _70504 _70505 _70507 _70506 _70508) : term713 _70506 _70508.
Proof. exact (conj (@lem5441891) (@lem5441821 _70504 _70505 _70507 _70506 _70508 h1)). Qed.
Lemma lem5441894 (x : real) (y : real) : term714 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5441895 (_70506 : int) (_70508 : int) : term715 _70506 _70508.
Proof. exact (@lem5441894 term227 (term331 _70506 _70508)). Qed.
Lemma lem5441896 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) (h1 : term626 _70504 _70505 _70507 _70506 _70508) : term716 _70506 _70508.
Proof. exact (@lem5441895 _70506 _70508 (@lem5441892 _70504 _70505 _70507 _70506 _70508 h1)). Qed.
Lemma lem5441897 (_70506 : int) (_70508 : int) : (term717 _70506 _70508) = (term331 _70506 _70508).
Proof. exact (@lem1982733 (term331 _70506 _70508)). Qed.
Lemma lem5441898 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5441899 (_70506 : int) (_70508 : int) : (term718 _70506 _70508) = (term333 _70506 _70508).
Proof. exact (MK_COMB (@lem5441898) (@lem5441897 _70506 _70508)). Qed.
Lemma lem5441900 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5441901 (_70506 : int) (_70508 : int) : (term716 _70506 _70508) = (term334 _70506 _70508).
Proof. exact (MK_COMB (@lem5441899 _70506 _70508) (@lem5441900)). Qed.
Lemma lem5441902 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) (h1 : term626 _70504 _70505 _70507 _70506 _70508) : term334 _70506 _70508.
Proof. exact (EQ_MP (@lem5441901 _70506 _70508) (@lem5441896 _70504 _70505 _70507 _70506 _70508 h1)). Qed.
Lemma lem5441904 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5441905 : term699 = term700.
Proof. exact (@lem5441904 term214 term227). Qed.
Lemma lem5441907 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5441908 : term227 = term320.
Proof. exact (@lem5441907 term228). Qed.
Lemma lem5441910 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5441911 : term214 = term291.
Proof. exact (@lem5441910 (NUMERAL 0)). Qed.
Lemma lem5441912 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5441913 : term701 = term702.
Proof. exact (MK_COMB (@lem5441912) (@lem5441911)). Qed.
Lemma lem5441914 : term700 = term703.
Proof. exact (MK_COMB (@lem5441913) (@lem5441908)). Qed.
Lemma lem5441915 : term704.
Proof. exact (@lem1980255 term214 term227 term227 term227). Qed.
Lemma lem5441917 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441918 : term700 = term706.
Proof. exact (@lem5441917 (NUMERAL 0) term228). Qed.
Lemma lem5441919 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441920 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441921 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441920 h1) (fun h1 : term706 = True => @lem5441919)). Qed.
Lemma lem5441922 : term706 = True.
Proof. exact (EQ_MP (@lem5441921) (@lem5441919)). Qed.
Lemma lem5441923 : term700 = True.
Proof. exact (TRANS (@lem5441918) (@lem5441922)). Qed.
Lemma lem5441924 : True = term700.
Proof. exact (SYM (@lem5441923)). Qed.
Lemma lem5441925 : term700.
Proof. exact (EQ_MP (@lem5441924) (@lem0)). Qed.
Lemma lem5441926 : term708.
Proof. exact (@lem5441915 (@lem5441925)). Qed.
Lemma lem5441928 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441929 : term700 = term706.
Proof. exact (@lem5441928 (NUMERAL 0) term228). Qed.
Lemma lem5441930 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441931 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441932 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441931 h1) (fun h1 : term706 = True => @lem5441930)). Qed.
Lemma lem5441933 : term706 = True.
Proof. exact (EQ_MP (@lem5441932) (@lem5441930)). Qed.
Lemma lem5441934 : term700 = True.
Proof. exact (TRANS (@lem5441929) (@lem5441933)). Qed.
Lemma lem5441935 : True = term700.
Proof. exact (SYM (@lem5441934)). Qed.
Lemma lem5441936 : term700.
Proof. exact (EQ_MP (@lem5441935) (@lem0)). Qed.
Lemma lem5441937 : term703 = term709.
Proof. exact (@lem5441926 (@lem5441936)). Qed.
Lemma lem5441939 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5441940 : term303 = term304.
Proof. exact (@lem5441939 term228 term228). Qed.
Lemma lem5441941 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5441942 : term306 = term228.
Proof. exact (EQ_MP (@lem5441941) (@lem940073)). Qed.
Lemma lem5441943 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5441944 : term304 = term227.
Proof. exact (MK_COMB (@lem5441943) (@lem5441942)). Qed.
Lemma lem5441945 : term303 = term227.
Proof. exact (TRANS (@lem5441940) (@lem5441944)). Qed.
Lemma lem5441947 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5441948 : term711 = term214.
Proof. exact (@lem5441947 term228). Qed.
Lemma lem5441949 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5441950 : term712 = term701.
Proof. exact (MK_COMB (@lem5441949) (@lem5441948)). Qed.
Lemma lem5441951 : term709 = term700.
Proof. exact (MK_COMB (@lem5441950) (@lem5441945)). Qed.
Lemma lem5441953 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441954 : term700 = term706.
Proof. exact (@lem5441953 (NUMERAL 0) term228). Qed.
Lemma lem5441955 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441956 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441957 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441956 h1) (fun h1 : term706 = True => @lem5441955)). Qed.
Lemma lem5441958 : term706 = True.
Proof. exact (EQ_MP (@lem5441957) (@lem5441955)). Qed.
Lemma lem5441959 : term700 = True.
Proof. exact (TRANS (@lem5441954) (@lem5441958)). Qed.
Lemma lem5441960 : term709 = True.
Proof. exact (TRANS (@lem5441951) (@lem5441959)). Qed.
Lemma lem5441961 : term703 = True.
Proof. exact (TRANS (@lem5441937) (@lem5441960)). Qed.
Lemma lem5441962 : term700 = True.
Proof. exact (TRANS (@lem5441914) (@lem5441961)). Qed.
Lemma lem5441963 : term699 = True.
Proof. exact (TRANS (@lem5441905) (@lem5441962)). Qed.
Lemma lem5441964 : True = term699.
Proof. exact (SYM (@lem5441963)). Qed.
Lemma lem5441965 : term699.
Proof. exact (EQ_MP (@lem5441964) (@lem0)). Qed.
Lemma lem5441966 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) (h1 : term626 _70504 _70505 _70507 _70506 _70508) : term719 _70506 _70508.
Proof. exact (conj (@lem5441965) (@lem5441828 _70504 _70505 _70507 _70506 _70508 h1)). Qed.
Lemma lem5441968 (x : real) (y : real) : term714 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5441969 (_70506 : int) (_70508 : int) : term720 _70506 _70508.
Proof. exact (@lem5441968 term227 (term363 _70506 _70508)). Qed.
Lemma lem5441970 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) (h1 : term626 _70504 _70505 _70507 _70506 _70508) : term721 _70506 _70508.
Proof. exact (@lem5441969 _70506 _70508 (@lem5441966 _70504 _70505 _70507 _70506 _70508 h1)). Qed.
Lemma lem5441971 (_70506 : int) (_70508 : int) : (term722 _70506 _70508) = (term363 _70506 _70508).
Proof. exact (@lem1982733 (term363 _70506 _70508)). Qed.
Lemma lem5441972 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5441973 (_70506 : int) (_70508 : int) : (term723 _70506 _70508) = (term365 _70506 _70508).
Proof. exact (MK_COMB (@lem5441972) (@lem5441971 _70506 _70508)). Qed.
Lemma lem5441974 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5441975 (_70506 : int) (_70508 : int) : (term721 _70506 _70508) = (term366 _70506 _70508).
Proof. exact (MK_COMB (@lem5441973 _70506 _70508) (@lem5441974)). Qed.
Lemma lem5441976 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) (h1 : term626 _70504 _70505 _70507 _70506 _70508) : term366 _70506 _70508.
Proof. exact (EQ_MP (@lem5441975 _70506 _70508) (@lem5441970 _70504 _70505 _70507 _70506 _70508 h1)). Qed.
Lemma lem5441977 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) (h1 : term626 _70504 _70505 _70507 _70506 _70508) : term724 _70506 _70508.
Proof. exact (conj (@lem5441976 _70504 _70505 _70507 _70506 _70508 h1) (@lem5441902 _70504 _70505 _70507 _70506 _70508 h1)). Qed.
Lemma lem5441979 (x : real) (y : real) : term725 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5441980 (_70506 : int) (_70508 : int) : term726 _70506 _70508.
Proof. exact (@lem5441979 (term363 _70506 _70508) (term331 _70506 _70508)). Qed.
Lemma lem5441981 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) (h1 : term626 _70504 _70505 _70507 _70506 _70508) : term727 _70506 _70508.
Proof. exact (@lem5441980 _70506 _70508 (@lem5441977 _70504 _70505 _70507 _70506 _70508 h1)). Qed.
Lemma lem5441982 (_70506 : int) (_70508 : int) : (term728 _70506 _70508) = (term729 _70506 _70508).
Proof. exact (@lem1982753 (term336 _70506) (real_of_int _70506) (real_of_int _70508) (term330 _70508)). Qed.
Lemma lem5441983 (_70506 : int) : (term730 _70506) = (term731 _70506).
Proof. exact (@lem1982713 term294 (real_of_int _70506)). Qed.
Lemma lem5441985 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5441986 : term227 = term320.
Proof. exact (@lem5441985 term228). Qed.
Lemma lem5441988 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5441989 : term294 = term295.
Proof. exact (@lem5441988 term228). Qed.
Lemma lem5441990 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5441991 : term732 = term733.
Proof. exact (MK_COMB (@lem5441990) (@lem5441989)). Qed.
Lemma lem5441992 : term734 = term735.
Proof. exact (MK_COMB (@lem5441991) (@lem5441986)). Qed.
Lemma lem5441993 : term736.
Proof. exact (@lem1981473 term294 term227 term227 term227 term214 term227). Qed.
Lemma lem5441995 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5441996 : term700 = term706.
Proof. exact (@lem5441995 (NUMERAL 0) term228). Qed.
Lemma lem5441997 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5441998 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5441999 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5441998 h1) (fun h1 : term706 = True => @lem5441997)). Qed.
Lemma lem5442000 : term706 = True.
Proof. exact (EQ_MP (@lem5441999) (@lem5441997)). Qed.
Lemma lem5442001 : term700 = True.
Proof. exact (TRANS (@lem5441996) (@lem5442000)). Qed.
Lemma lem5442002 : True = term700.
Proof. exact (SYM (@lem5442001)). Qed.
Lemma lem5442003 : term700.
Proof. exact (EQ_MP (@lem5442002) (@lem0)). Qed.
Lemma lem5442004 : term737.
Proof. exact (@lem5441993 (@lem5442003)). Qed.
Lemma lem5442006 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442007 : term700 = term706.
Proof. exact (@lem5442006 (NUMERAL 0) term228). Qed.
Lemma lem5442008 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442009 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442010 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442009 h1) (fun h1 : term706 = True => @lem5442008)). Qed.
Lemma lem5442011 : term706 = True.
Proof. exact (EQ_MP (@lem5442010) (@lem5442008)). Qed.
Lemma lem5442012 : term700 = True.
Proof. exact (TRANS (@lem5442007) (@lem5442011)). Qed.
Lemma lem5442013 : True = term700.
Proof. exact (SYM (@lem5442012)). Qed.
Lemma lem5442014 : term700.
Proof. exact (EQ_MP (@lem5442013) (@lem0)). Qed.
Lemma lem5442015 : term738.
Proof. exact (@lem5442004 (@lem5442014)). Qed.
Lemma lem5442017 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442018 : term700 = term706.
Proof. exact (@lem5442017 (NUMERAL 0) term228). Qed.
Lemma lem5442019 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442020 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442021 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442020 h1) (fun h1 : term706 = True => @lem5442019)). Qed.
Lemma lem5442022 : term706 = True.
Proof. exact (EQ_MP (@lem5442021) (@lem5442019)). Qed.
Lemma lem5442023 : term700 = True.
Proof. exact (TRANS (@lem5442018) (@lem5442022)). Qed.
Lemma lem5442024 : True = term700.
Proof. exact (SYM (@lem5442023)). Qed.
Lemma lem5442025 : term700.
Proof. exact (EQ_MP (@lem5442024) (@lem0)). Qed.
Lemma lem5442026 : term739.
Proof. exact (@lem5442015 (@lem5442025)). Qed.
Lemma lem5442028 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5442029 : term303 = term304.
Proof. exact (@lem5442028 term228 term228). Qed.
Lemma lem5442030 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5442031 : term306 = term228.
Proof. exact (EQ_MP (@lem5442030) (@lem940073)). Qed.
Lemma lem5442032 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5442033 : term304 = term227.
Proof. exact (MK_COMB (@lem5442032) (@lem5442031)). Qed.
Lemma lem5442034 : term303 = term227.
Proof. exact (TRANS (@lem5442029) (@lem5442033)). Qed.
Lemma lem5442036 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5442037 : term321 = term326.
Proof. exact (@lem5442036 term228 term228). Qed.
Lemma lem5442038 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5442039 : term306 = term228.
Proof. exact (EQ_MP (@lem5442038) (@lem940073)). Qed.
Lemma lem5442040 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5442041 : term304 = term227.
Proof. exact (MK_COMB (@lem5442040) (@lem5442039)). Qed.
Lemma lem5442042 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5442043 : term326 = term294.
Proof. exact (MK_COMB (@lem5442042) (@lem5442041)). Qed.
Lemma lem5442044 : term321 = term294.
Proof. exact (TRANS (@lem5442037) (@lem5442043)). Qed.
Lemma lem5442045 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5442046 : term740 = term732.
Proof. exact (MK_COMB (@lem5442045) (@lem5442044)). Qed.
Lemma lem5442047 : term741 = term734.
Proof. exact (MK_COMB (@lem5442046) (@lem5442034)). Qed.
Lemma lem5442049 (m : nat) : (term742 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5442050 : term734 = term214.
Proof. exact (@lem5442049 term228). Qed.
Lemma lem5442051 : term741 = term214.
Proof. exact (TRANS (@lem5442047) (@lem5442050)). Qed.
Lemma lem5442052 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5442053 : term743 = term744.
Proof. exact (MK_COMB (@lem5442052) (@lem5442051)). Qed.
Lemma lem5442054 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem5442055 : term745 = term711.
Proof. exact (MK_COMB (@lem5442053) (@lem5442054)). Qed.
Lemma lem5442057 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5442058 : term711 = term214.
Proof. exact (@lem5442057 term228). Qed.
Lemma lem5442059 : term745 = term214.
Proof. exact (TRANS (@lem5442055) (@lem5442058)). Qed.
Lemma lem5442061 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5442062 : term303 = term304.
Proof. exact (@lem5442061 term228 term228). Qed.
Lemma lem5442063 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5442064 : term306 = term228.
Proof. exact (EQ_MP (@lem5442063) (@lem940073)). Qed.
Lemma lem5442065 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5442066 : term304 = term227.
Proof. exact (MK_COMB (@lem5442065) (@lem5442064)). Qed.
Lemma lem5442067 : term303 = term227.
Proof. exact (TRANS (@lem5442062) (@lem5442066)). Qed.
Lemma lem5442068 : term744 = term744.
Proof. exact (eq_refl term744). Qed.
Lemma lem5442069 : term746 = term711.
Proof. exact (MK_COMB (@lem5442068) (@lem5442067)). Qed.
Lemma lem5442071 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5442072 : term711 = term214.
Proof. exact (@lem5442071 term228). Qed.
Lemma lem5442073 : term746 = term214.
Proof. exact (TRANS (@lem5442069) (@lem5442072)). Qed.
Lemma lem5442074 : term214 = term746.
Proof. exact (SYM (@lem5442073)). Qed.
Lemma lem5442075 : term745 = term746.
Proof. exact (TRANS (@lem5442059) (@lem5442074)). Qed.
Lemma lem5442076 : term735 = term291.
Proof. exact (@lem5442026 (@lem5442075)). Qed.
Lemma lem5442077 : term734 = term291.
Proof. exact (TRANS (@lem5441992) (@lem5442076)). Qed.
Lemma lem5442079 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5442080 : term291 = term214.
Proof. exact (@lem5442079 term214). Qed.
Lemma lem5442081 : term734 = term214.
Proof. exact (TRANS (@lem5442077) (@lem5442080)). Qed.
Lemma lem5442082 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5442083 : term747 = term744.
Proof. exact (MK_COMB (@lem5442082) (@lem5442081)). Qed.
Lemma lem5442084 (_70506 : int) : (real_of_int _70506) = (real_of_int _70506).
Proof. exact (eq_refl (real_of_int _70506)). Qed.
Lemma lem5442085 (_70506 : int) : (term731 _70506) = (term748 _70506).
Proof. exact (MK_COMB (@lem5442083) (@lem5442084 _70506)). Qed.
Lemma lem5442086 (_70506 : int) : (term730 _70506) = (term748 _70506).
Proof. exact (TRANS (@lem5441983 _70506) (@lem5442085 _70506)). Qed.
Lemma lem5442087 (_70506 : int) : (term748 _70506) = term214.
Proof. exact (@lem1982719 (real_of_int _70506)). Qed.
Lemma lem5442088 (_70506 : int) : (term730 _70506) = term214.
Proof. exact (TRANS (@lem5442086 _70506) (@lem5442087 _70506)). Qed.
Lemma lem5442089 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5442090 (_70506 : int) : (term749 _70506) = term750.
Proof. exact (MK_COMB (@lem5442089) (@lem5442088 _70506)). Qed.
Lemma lem5442091 (_70508 : int) : (term751 _70508) = (term752 _70508).
Proof. exact (@lem1982763 (real_of_int _70508) (term336 _70508) term294). Qed.
Lemma lem5442092 (_70508 : int) : (term753 _70508) = (term731 _70508).
Proof. exact (@lem1982715 term294 (real_of_int _70508)). Qed.
Lemma lem5442094 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5442095 : term227 = term320.
Proof. exact (@lem5442094 term228). Qed.
Lemma lem5442097 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5442098 : term294 = term295.
Proof. exact (@lem5442097 term228). Qed.
Lemma lem5442099 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5442100 : term732 = term733.
Proof. exact (MK_COMB (@lem5442099) (@lem5442098)). Qed.
Lemma lem5442101 : term734 = term735.
Proof. exact (MK_COMB (@lem5442100) (@lem5442095)). Qed.
Lemma lem5442102 : term736.
Proof. exact (@lem1981473 term294 term227 term227 term227 term214 term227). Qed.
Lemma lem5442104 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442105 : term700 = term706.
Proof. exact (@lem5442104 (NUMERAL 0) term228). Qed.
Lemma lem5442106 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442107 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442108 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442107 h1) (fun h1 : term706 = True => @lem5442106)). Qed.
Lemma lem5442109 : term706 = True.
Proof. exact (EQ_MP (@lem5442108) (@lem5442106)). Qed.
Lemma lem5442110 : term700 = True.
Proof. exact (TRANS (@lem5442105) (@lem5442109)). Qed.
Lemma lem5442111 : True = term700.
Proof. exact (SYM (@lem5442110)). Qed.
Lemma lem5442112 : term700.
Proof. exact (EQ_MP (@lem5442111) (@lem0)). Qed.
Lemma lem5442113 : term737.
Proof. exact (@lem5442102 (@lem5442112)). Qed.
Lemma lem5442115 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442116 : term700 = term706.
Proof. exact (@lem5442115 (NUMERAL 0) term228). Qed.
Lemma lem5442117 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442118 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442119 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442118 h1) (fun h1 : term706 = True => @lem5442117)). Qed.
Lemma lem5442120 : term706 = True.
Proof. exact (EQ_MP (@lem5442119) (@lem5442117)). Qed.
Lemma lem5442121 : term700 = True.
Proof. exact (TRANS (@lem5442116) (@lem5442120)). Qed.
Lemma lem5442122 : True = term700.
Proof. exact (SYM (@lem5442121)). Qed.
Lemma lem5442123 : term700.
Proof. exact (EQ_MP (@lem5442122) (@lem0)). Qed.
Lemma lem5442124 : term738.
Proof. exact (@lem5442113 (@lem5442123)). Qed.
Lemma lem5442126 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442127 : term700 = term706.
Proof. exact (@lem5442126 (NUMERAL 0) term228). Qed.
Lemma lem5442128 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442129 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442130 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442129 h1) (fun h1 : term706 = True => @lem5442128)). Qed.
Lemma lem5442131 : term706 = True.
Proof. exact (EQ_MP (@lem5442130) (@lem5442128)). Qed.
Lemma lem5442132 : term700 = True.
Proof. exact (TRANS (@lem5442127) (@lem5442131)). Qed.
Lemma lem5442133 : True = term700.
Proof. exact (SYM (@lem5442132)). Qed.
Lemma lem5442134 : term700.
Proof. exact (EQ_MP (@lem5442133) (@lem0)). Qed.
Lemma lem5442135 : term739.
Proof. exact (@lem5442124 (@lem5442134)). Qed.
Lemma lem5442137 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5442138 : term303 = term304.
Proof. exact (@lem5442137 term228 term228). Qed.
Lemma lem5442139 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5442140 : term306 = term228.
Proof. exact (EQ_MP (@lem5442139) (@lem940073)). Qed.
Lemma lem5442141 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5442142 : term304 = term227.
Proof. exact (MK_COMB (@lem5442141) (@lem5442140)). Qed.
Lemma lem5442143 : term303 = term227.
Proof. exact (TRANS (@lem5442138) (@lem5442142)). Qed.
Lemma lem5442145 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5442146 : term321 = term326.
Proof. exact (@lem5442145 term228 term228). Qed.
Lemma lem5442147 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5442148 : term306 = term228.
Proof. exact (EQ_MP (@lem5442147) (@lem940073)). Qed.
Lemma lem5442149 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5442150 : term304 = term227.
Proof. exact (MK_COMB (@lem5442149) (@lem5442148)). Qed.
Lemma lem5442151 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5442152 : term326 = term294.
Proof. exact (MK_COMB (@lem5442151) (@lem5442150)). Qed.
Lemma lem5442153 : term321 = term294.
Proof. exact (TRANS (@lem5442146) (@lem5442152)). Qed.
Lemma lem5442154 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5442155 : term740 = term732.
Proof. exact (MK_COMB (@lem5442154) (@lem5442153)). Qed.
Lemma lem5442156 : term741 = term734.
Proof. exact (MK_COMB (@lem5442155) (@lem5442143)). Qed.
Lemma lem5442158 (m : nat) : (term742 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5442159 : term734 = term214.
Proof. exact (@lem5442158 term228). Qed.
Lemma lem5442160 : term741 = term214.
Proof. exact (TRANS (@lem5442156) (@lem5442159)). Qed.
Lemma lem5442161 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5442162 : term743 = term744.
Proof. exact (MK_COMB (@lem5442161) (@lem5442160)). Qed.
Lemma lem5442163 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem5442164 : term745 = term711.
Proof. exact (MK_COMB (@lem5442162) (@lem5442163)). Qed.
Lemma lem5442166 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5442167 : term711 = term214.
Proof. exact (@lem5442166 term228). Qed.
Lemma lem5442168 : term745 = term214.
Proof. exact (TRANS (@lem5442164) (@lem5442167)). Qed.
Lemma lem5442170 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5442171 : term303 = term304.
Proof. exact (@lem5442170 term228 term228). Qed.
Lemma lem5442172 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5442173 : term306 = term228.
Proof. exact (EQ_MP (@lem5442172) (@lem940073)). Qed.
Lemma lem5442174 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5442175 : term304 = term227.
Proof. exact (MK_COMB (@lem5442174) (@lem5442173)). Qed.
Lemma lem5442176 : term303 = term227.
Proof. exact (TRANS (@lem5442171) (@lem5442175)). Qed.
Lemma lem5442177 : term744 = term744.
Proof. exact (eq_refl term744). Qed.
Lemma lem5442178 : term746 = term711.
Proof. exact (MK_COMB (@lem5442177) (@lem5442176)). Qed.
Lemma lem5442180 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5442181 : term711 = term214.
Proof. exact (@lem5442180 term228). Qed.
Lemma lem5442182 : term746 = term214.
Proof. exact (TRANS (@lem5442178) (@lem5442181)). Qed.
Lemma lem5442183 : term214 = term746.
Proof. exact (SYM (@lem5442182)). Qed.
Lemma lem5442184 : term745 = term746.
Proof. exact (TRANS (@lem5442168) (@lem5442183)). Qed.
Lemma lem5442185 : term735 = term291.
Proof. exact (@lem5442135 (@lem5442184)). Qed.
Lemma lem5442186 : term734 = term291.
Proof. exact (TRANS (@lem5442101) (@lem5442185)). Qed.
Lemma lem5442188 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5442189 : term291 = term214.
Proof. exact (@lem5442188 term214). Qed.
Lemma lem5442190 : term734 = term214.
Proof. exact (TRANS (@lem5442186) (@lem5442189)). Qed.
Lemma lem5442191 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5442192 : term747 = term744.
Proof. exact (MK_COMB (@lem5442191) (@lem5442190)). Qed.
Lemma lem5442193 (_70508 : int) : (real_of_int _70508) = (real_of_int _70508).
Proof. exact (eq_refl (real_of_int _70508)). Qed.
Lemma lem5442194 (_70508 : int) : (term731 _70508) = (term748 _70508).
Proof. exact (MK_COMB (@lem5442192) (@lem5442193 _70508)). Qed.
Lemma lem5442195 (_70508 : int) : (term753 _70508) = (term748 _70508).
Proof. exact (TRANS (@lem5442092 _70508) (@lem5442194 _70508)). Qed.
Lemma lem5442196 (_70508 : int) : (term748 _70508) = term214.
Proof. exact (@lem1982719 (real_of_int _70508)). Qed.
Lemma lem5442197 (_70508 : int) : (term753 _70508) = term214.
Proof. exact (TRANS (@lem5442195 _70508) (@lem5442196 _70508)). Qed.
Lemma lem5442198 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5442199 (_70508 : int) : (term754 _70508) = term750.
Proof. exact (MK_COMB (@lem5442198) (@lem5442197 _70508)). Qed.
Lemma lem5442200 : term294 = term294.
Proof. exact (eq_refl term294). Qed.
Lemma lem5442201 (_70508 : int) : (term752 _70508) = term755.
Proof. exact (MK_COMB (@lem5442199 _70508) (@lem5442200)). Qed.
Lemma lem5442202 (_70508 : int) : (term751 _70508) = term755.
Proof. exact (TRANS (@lem5442091 _70508) (@lem5442201 _70508)). Qed.
Lemma lem5442203 : term755 = term294.
Proof. exact (@lem1982721 term294). Qed.
Lemma lem5442204 (_70508 : int) : (term751 _70508) = term294.
Proof. exact (TRANS (@lem5442202 _70508) (@lem5442203)). Qed.
Lemma lem5442205 (_70506 : int) (_70508 : int) : (term729 _70506 _70508) = term755.
Proof. exact (MK_COMB (@lem5442090 _70506) (@lem5442204 _70508)). Qed.
Lemma lem5442206 (_70506 : int) (_70508 : int) : (term728 _70506 _70508) = term755.
Proof. exact (TRANS (@lem5441982 _70506 _70508) (@lem5442205 _70506 _70508)). Qed.
Lemma lem5442207 : term755 = term294.
Proof. exact (@lem1982721 term294). Qed.
Lemma lem5442208 (_70506 : int) (_70508 : int) : (term728 _70506 _70508) = term294.
Proof. exact (TRANS (@lem5442206 _70506 _70508) (@lem5442207)). Qed.
Lemma lem5442209 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5442210 (_70506 : int) (_70508 : int) : (term756 _70506 _70508) = term757.
Proof. exact (MK_COMB (@lem5442209) (@lem5442208 _70506 _70508)). Qed.
Lemma lem5442211 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5442212 (_70506 : int) (_70508 : int) : (term727 _70506 _70508) = term758.
Proof. exact (MK_COMB (@lem5442210 _70506 _70508) (@lem5442211)). Qed.
Lemma lem5442213 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) (h1 : term626 _70504 _70505 _70507 _70506 _70508) : term758.
Proof. exact (EQ_MP (@lem5442212 _70506 _70508) (@lem5441981 _70504 _70505 _70507 _70506 _70508 h1)). Qed.
Lemma lem5442215 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5442216 : term758 = term759.
Proof. exact (@lem5442215 term214 term294). Qed.
Lemma lem5442218 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5442219 : term294 = term295.
Proof. exact (@lem5442218 term228). Qed.
Lemma lem5442221 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5442222 : term214 = term291.
Proof. exact (@lem5442221 (NUMERAL 0)). Qed.
Lemma lem5442223 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5442224 : term216 = term760.
Proof. exact (MK_COMB (@lem5442223) (@lem5442222)). Qed.
Lemma lem5442225 : term759 = term761.
Proof. exact (MK_COMB (@lem5442224) (@lem5442219)). Qed.
Lemma lem5442226 : term762.
Proof. exact (@lem1980026 term214 term227 term294 term227). Qed.
Lemma lem5442228 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442229 : term700 = term706.
Proof. exact (@lem5442228 (NUMERAL 0) term228). Qed.
Lemma lem5442230 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442231 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442232 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442231 h1) (fun h1 : term706 = True => @lem5442230)). Qed.
Lemma lem5442233 : term706 = True.
Proof. exact (EQ_MP (@lem5442232) (@lem5442230)). Qed.
Lemma lem5442234 : term700 = True.
Proof. exact (TRANS (@lem5442229) (@lem5442233)). Qed.
Lemma lem5442235 : True = term700.
Proof. exact (SYM (@lem5442234)). Qed.
Lemma lem5442236 : term700.
Proof. exact (EQ_MP (@lem5442235) (@lem0)). Qed.
Lemma lem5442237 : term763.
Proof. exact (@lem5442226 (@lem5442236)). Qed.
Lemma lem5442239 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442240 : term700 = term706.
Proof. exact (@lem5442239 (NUMERAL 0) term228). Qed.
Lemma lem5442241 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442242 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442243 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442242 h1) (fun h1 : term706 = True => @lem5442241)). Qed.
Lemma lem5442244 : term706 = True.
Proof. exact (EQ_MP (@lem5442243) (@lem5442241)). Qed.
Lemma lem5442245 : term700 = True.
Proof. exact (TRANS (@lem5442240) (@lem5442244)). Qed.
Lemma lem5442246 : True = term700.
Proof. exact (SYM (@lem5442245)). Qed.
Lemma lem5442247 : term700.
Proof. exact (EQ_MP (@lem5442246) (@lem0)). Qed.
Lemma lem5442248 : term761 = term764.
Proof. exact (@lem5442237 (@lem5442247)). Qed.
Lemma lem5442250 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5442251 : term321 = term326.
Proof. exact (@lem5442250 term228 term228). Qed.
Lemma lem5442252 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5442253 : term306 = term228.
Proof. exact (EQ_MP (@lem5442252) (@lem940073)). Qed.
Lemma lem5442254 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5442255 : term304 = term227.
Proof. exact (MK_COMB (@lem5442254) (@lem5442253)). Qed.
Lemma lem5442256 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5442257 : term326 = term294.
Proof. exact (MK_COMB (@lem5442256) (@lem5442255)). Qed.
Lemma lem5442258 : term321 = term294.
Proof. exact (TRANS (@lem5442251) (@lem5442257)). Qed.
Lemma lem5442260 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5442261 : term711 = term214.
Proof. exact (@lem5442260 term228). Qed.
Lemma lem5442262 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5442263 : term765 = term216.
Proof. exact (MK_COMB (@lem5442262) (@lem5442261)). Qed.
Lemma lem5442264 : term764 = term759.
Proof. exact (MK_COMB (@lem5442263) (@lem5442258)). Qed.
Lemma lem5442266 (m : nat) (n : nat) : (term766 m n) = (term767 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5442267 : term759 = term768.
Proof. exact (@lem5442266 (NUMERAL 0) term228). Qed.
Lemma lem5442268 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442269 (h1 : term707 = (BIT1 0)) : (term228 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5442270 : (term707 = (BIT1 0)) = ((term228 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442269 h1) (fun h1 : (term228 = (NUMERAL 0)) = False => @lem5442268)). Qed.
Lemma lem5442271 : (term228 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5442270) (@lem5442268)). Qed.
Lemma lem5442272 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5442273 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5442274 : term769 = (and True).
Proof. exact (MK_COMB (@lem5442273) (@lem5442272)). Qed.
Lemma lem5442275 : term768 = (True /\ False).
Proof. exact (MK_COMB (@lem5442274) (@lem5442271)). Qed.
Lemma lem5442277 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5442278 : term768 = False.
Proof. exact (TRANS (@lem5442275) (@lem5442277)). Qed.
Lemma lem5442279 : term759 = False.
Proof. exact (TRANS (@lem5442267) (@lem5442278)). Qed.
Lemma lem5442280 : term764 = False.
Proof. exact (TRANS (@lem5442264) (@lem5442279)). Qed.
Lemma lem5442281 : term761 = False.
Proof. exact (TRANS (@lem5442248) (@lem5442280)). Qed.
Lemma lem5442282 : term759 = False.
Proof. exact (TRANS (@lem5442225) (@lem5442281)). Qed.
Lemma lem5442283 : term758 = False.
Proof. exact (TRANS (@lem5442216) (@lem5442282)). Qed.
Lemma lem5442284 (_70504 : int) (_70505 : int) (_70507 : int) (_70506 : int) (_70508 : int) (h1 : term626 _70504 _70505 _70507 _70506 _70508) : False.
Proof. exact (EQ_MP (@lem5442283) (@lem5442213 _70504 _70505 _70507 _70506 _70508 h1)). Qed.
Lemma lem5442285 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) (h1 : term644 _70505 _70506 _70507 _70504 _70508) : term644 _70505 _70506 _70507 _70504 _70508.
Proof. exact (h1). Qed.
Lemma lem5442286 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) (h1 : term644 _70505 _70506 _70507 _70504 _70508) : term642 _70505 _70506 _70507 _70504 _70508.
Proof. exact (proj2 (@lem5442285 _70505 _70506 _70507 _70504 _70508 h1)). Qed.
Lemma lem5442288 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) (h1 : term644 _70505 _70506 _70507 _70504 _70508) : term641 _70505 _70506 _70507 _70504 _70508.
Proof. exact (proj2 (@lem5442286 _70505 _70506 _70507 _70504 _70508 h1)). Qed.
Lemma lem5442290 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) (h1 : term644 _70505 _70506 _70507 _70504 _70508) : term639 _70505 _70506 _70507 _70504 _70508.
Proof. exact (proj2 (@lem5442288 _70505 _70506 _70507 _70504 _70508 h1)). Qed.
Lemma lem5442292 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) (h1 : term644 _70505 _70506 _70507 _70504 _70508) : term637 _70505 _70506 _70507 _70504 _70508.
Proof. exact (proj2 (@lem5442290 _70505 _70506 _70507 _70504 _70508 h1)). Qed.
Lemma lem5442294 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) (h1 : term644 _70505 _70506 _70507 _70504 _70508) : term635 _70505 _70506 _70507 _70504 _70508.
Proof. exact (proj2 (@lem5442292 _70505 _70506 _70507 _70504 _70508 h1)). Qed.
Lemma lem5442296 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) (h1 : term644 _70505 _70506 _70507 _70504 _70508) : term633 _70505 _70506 _70507 _70504 _70508.
Proof. exact (proj2 (@lem5442294 _70505 _70506 _70507 _70504 _70508 h1)). Qed.
Lemma lem5442298 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) (h1 : term644 _70505 _70506 _70507 _70504 _70508) : term334 _70504 _70508.
Proof. exact (proj2 (@lem5442296 _70505 _70506 _70507 _70504 _70508 h1)). Qed.
Lemma lem5442299 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) (h1 : term644 _70505 _70506 _70507 _70504 _70508) : term372 _70504 _70505 _70506 _70507 _70508.
Proof. exact (proj1 (@lem5442296 _70505 _70506 _70507 _70504 _70508 h1)). Qed.
Lemma lem5442301 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) (h1 : term644 _70505 _70506 _70507 _70504 _70508) : term370 _70504 _70505 _70508.
Proof. exact (proj1 (@lem5442299 _70505 _70506 _70507 _70504 _70508 h1)). Qed.
Lemma lem5442303 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) (h1 : term644 _70505 _70506 _70507 _70504 _70508) : term366 _70504 _70508.
Proof. exact (proj1 (@lem5442301 _70505 _70506 _70507 _70504 _70508 h1)). Qed.
Lemma lem5442307 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5442308 : term699 = term700.
Proof. exact (@lem5442307 term214 term227). Qed.
Lemma lem5442310 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5442311 : term227 = term320.
Proof. exact (@lem5442310 term228). Qed.
Lemma lem5442313 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5442314 : term214 = term291.
Proof. exact (@lem5442313 (NUMERAL 0)). Qed.
Lemma lem5442315 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5442316 : term701 = term702.
Proof. exact (MK_COMB (@lem5442315) (@lem5442314)). Qed.
Lemma lem5442317 : term700 = term703.
Proof. exact (MK_COMB (@lem5442316) (@lem5442311)). Qed.
Lemma lem5442318 : term704.
Proof. exact (@lem1980255 term214 term227 term227 term227). Qed.
Lemma lem5442320 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442321 : term700 = term706.
Proof. exact (@lem5442320 (NUMERAL 0) term228). Qed.
Lemma lem5442322 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442323 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442324 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442323 h1) (fun h1 : term706 = True => @lem5442322)). Qed.
Lemma lem5442325 : term706 = True.
Proof. exact (EQ_MP (@lem5442324) (@lem5442322)). Qed.
Lemma lem5442326 : term700 = True.
Proof. exact (TRANS (@lem5442321) (@lem5442325)). Qed.
Lemma lem5442327 : True = term700.
Proof. exact (SYM (@lem5442326)). Qed.
Lemma lem5442328 : term700.
Proof. exact (EQ_MP (@lem5442327) (@lem0)). Qed.
Lemma lem5442329 : term708.
Proof. exact (@lem5442318 (@lem5442328)). Qed.
Lemma lem5442331 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442332 : term700 = term706.
Proof. exact (@lem5442331 (NUMERAL 0) term228). Qed.
Lemma lem5442333 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442334 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442335 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442334 h1) (fun h1 : term706 = True => @lem5442333)). Qed.
Lemma lem5442336 : term706 = True.
Proof. exact (EQ_MP (@lem5442335) (@lem5442333)). Qed.
Lemma lem5442337 : term700 = True.
Proof. exact (TRANS (@lem5442332) (@lem5442336)). Qed.
Lemma lem5442338 : True = term700.
Proof. exact (SYM (@lem5442337)). Qed.
Lemma lem5442339 : term700.
Proof. exact (EQ_MP (@lem5442338) (@lem0)). Qed.
Lemma lem5442340 : term703 = term709.
Proof. exact (@lem5442329 (@lem5442339)). Qed.
Lemma lem5442342 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5442343 : term303 = term304.
Proof. exact (@lem5442342 term228 term228). Qed.
Lemma lem5442344 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5442345 : term306 = term228.
Proof. exact (EQ_MP (@lem5442344) (@lem940073)). Qed.
Lemma lem5442346 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5442347 : term304 = term227.
Proof. exact (MK_COMB (@lem5442346) (@lem5442345)). Qed.
Lemma lem5442348 : term303 = term227.
Proof. exact (TRANS (@lem5442343) (@lem5442347)). Qed.
Lemma lem5442350 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5442351 : term711 = term214.
Proof. exact (@lem5442350 term228). Qed.
Lemma lem5442352 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5442353 : term712 = term701.
Proof. exact (MK_COMB (@lem5442352) (@lem5442351)). Qed.
Lemma lem5442354 : term709 = term700.
Proof. exact (MK_COMB (@lem5442353) (@lem5442348)). Qed.
Lemma lem5442356 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442357 : term700 = term706.
Proof. exact (@lem5442356 (NUMERAL 0) term228). Qed.
Lemma lem5442358 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442359 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442360 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442359 h1) (fun h1 : term706 = True => @lem5442358)). Qed.
Lemma lem5442361 : term706 = True.
Proof. exact (EQ_MP (@lem5442360) (@lem5442358)). Qed.
Lemma lem5442362 : term700 = True.
Proof. exact (TRANS (@lem5442357) (@lem5442361)). Qed.
Lemma lem5442363 : term709 = True.
Proof. exact (TRANS (@lem5442354) (@lem5442362)). Qed.
Lemma lem5442364 : term703 = True.
Proof. exact (TRANS (@lem5442340) (@lem5442363)). Qed.
Lemma lem5442365 : term700 = True.
Proof. exact (TRANS (@lem5442317) (@lem5442364)). Qed.
Lemma lem5442366 : term699 = True.
Proof. exact (TRANS (@lem5442308) (@lem5442365)). Qed.
Lemma lem5442367 : True = term699.
Proof. exact (SYM (@lem5442366)). Qed.
Lemma lem5442368 : term699.
Proof. exact (EQ_MP (@lem5442367) (@lem0)). Qed.
Lemma lem5442369 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) (h1 : term644 _70505 _70506 _70507 _70504 _70508) : term713 _70504 _70508.
Proof. exact (conj (@lem5442368) (@lem5442298 _70505 _70506 _70507 _70504 _70508 h1)). Qed.
Lemma lem5442371 (x : real) (y : real) : term714 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5442372 (_70504 : int) (_70508 : int) : term715 _70504 _70508.
Proof. exact (@lem5442371 term227 (term331 _70504 _70508)). Qed.
Lemma lem5442373 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) (h1 : term644 _70505 _70506 _70507 _70504 _70508) : term716 _70504 _70508.
Proof. exact (@lem5442372 _70504 _70508 (@lem5442369 _70505 _70506 _70507 _70504 _70508 h1)). Qed.
Lemma lem5442374 (_70504 : int) (_70508 : int) : (term717 _70504 _70508) = (term331 _70504 _70508).
Proof. exact (@lem1982733 (term331 _70504 _70508)). Qed.
Lemma lem5442375 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5442376 (_70504 : int) (_70508 : int) : (term718 _70504 _70508) = (term333 _70504 _70508).
Proof. exact (MK_COMB (@lem5442375) (@lem5442374 _70504 _70508)). Qed.
Lemma lem5442377 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5442378 (_70504 : int) (_70508 : int) : (term716 _70504 _70508) = (term334 _70504 _70508).
Proof. exact (MK_COMB (@lem5442376 _70504 _70508) (@lem5442377)). Qed.
Lemma lem5442379 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) (h1 : term644 _70505 _70506 _70507 _70504 _70508) : term334 _70504 _70508.
Proof. exact (EQ_MP (@lem5442378 _70504 _70508) (@lem5442373 _70505 _70506 _70507 _70504 _70508 h1)). Qed.
Lemma lem5442381 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5442382 : term699 = term700.
Proof. exact (@lem5442381 term214 term227). Qed.
Lemma lem5442384 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5442385 : term227 = term320.
Proof. exact (@lem5442384 term228). Qed.
Lemma lem5442387 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5442388 : term214 = term291.
Proof. exact (@lem5442387 (NUMERAL 0)). Qed.
Lemma lem5442389 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5442390 : term701 = term702.
Proof. exact (MK_COMB (@lem5442389) (@lem5442388)). Qed.
Lemma lem5442391 : term700 = term703.
Proof. exact (MK_COMB (@lem5442390) (@lem5442385)). Qed.
Lemma lem5442392 : term704.
Proof. exact (@lem1980255 term214 term227 term227 term227). Qed.
Lemma lem5442394 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442395 : term700 = term706.
Proof. exact (@lem5442394 (NUMERAL 0) term228). Qed.
Lemma lem5442396 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442397 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442398 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442397 h1) (fun h1 : term706 = True => @lem5442396)). Qed.
Lemma lem5442399 : term706 = True.
Proof. exact (EQ_MP (@lem5442398) (@lem5442396)). Qed.
Lemma lem5442400 : term700 = True.
Proof. exact (TRANS (@lem5442395) (@lem5442399)). Qed.
Lemma lem5442401 : True = term700.
Proof. exact (SYM (@lem5442400)). Qed.
Lemma lem5442402 : term700.
Proof. exact (EQ_MP (@lem5442401) (@lem0)). Qed.
Lemma lem5442403 : term708.
Proof. exact (@lem5442392 (@lem5442402)). Qed.
Lemma lem5442405 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442406 : term700 = term706.
Proof. exact (@lem5442405 (NUMERAL 0) term228). Qed.
Lemma lem5442407 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442408 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442409 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442408 h1) (fun h1 : term706 = True => @lem5442407)). Qed.
Lemma lem5442410 : term706 = True.
Proof. exact (EQ_MP (@lem5442409) (@lem5442407)). Qed.
Lemma lem5442411 : term700 = True.
Proof. exact (TRANS (@lem5442406) (@lem5442410)). Qed.
Lemma lem5442412 : True = term700.
Proof. exact (SYM (@lem5442411)). Qed.
Lemma lem5442413 : term700.
Proof. exact (EQ_MP (@lem5442412) (@lem0)). Qed.
Lemma lem5442414 : term703 = term709.
Proof. exact (@lem5442403 (@lem5442413)). Qed.
Lemma lem5442416 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5442417 : term303 = term304.
Proof. exact (@lem5442416 term228 term228). Qed.
Lemma lem5442418 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5442419 : term306 = term228.
Proof. exact (EQ_MP (@lem5442418) (@lem940073)). Qed.
Lemma lem5442420 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5442421 : term304 = term227.
Proof. exact (MK_COMB (@lem5442420) (@lem5442419)). Qed.
Lemma lem5442422 : term303 = term227.
Proof. exact (TRANS (@lem5442417) (@lem5442421)). Qed.
Lemma lem5442424 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5442425 : term711 = term214.
Proof. exact (@lem5442424 term228). Qed.
Lemma lem5442426 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5442427 : term712 = term701.
Proof. exact (MK_COMB (@lem5442426) (@lem5442425)). Qed.
Lemma lem5442428 : term709 = term700.
Proof. exact (MK_COMB (@lem5442427) (@lem5442422)). Qed.
Lemma lem5442430 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442431 : term700 = term706.
Proof. exact (@lem5442430 (NUMERAL 0) term228). Qed.
Lemma lem5442432 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442433 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442434 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442433 h1) (fun h1 : term706 = True => @lem5442432)). Qed.
Lemma lem5442435 : term706 = True.
Proof. exact (EQ_MP (@lem5442434) (@lem5442432)). Qed.
Lemma lem5442436 : term700 = True.
Proof. exact (TRANS (@lem5442431) (@lem5442435)). Qed.
Lemma lem5442437 : term709 = True.
Proof. exact (TRANS (@lem5442428) (@lem5442436)). Qed.
Lemma lem5442438 : term703 = True.
Proof. exact (TRANS (@lem5442414) (@lem5442437)). Qed.
Lemma lem5442439 : term700 = True.
Proof. exact (TRANS (@lem5442391) (@lem5442438)). Qed.
Lemma lem5442440 : term699 = True.
Proof. exact (TRANS (@lem5442382) (@lem5442439)). Qed.
Lemma lem5442441 : True = term699.
Proof. exact (SYM (@lem5442440)). Qed.
Lemma lem5442442 : term699.
Proof. exact (EQ_MP (@lem5442441) (@lem0)). Qed.
Lemma lem5442443 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) (h1 : term644 _70505 _70506 _70507 _70504 _70508) : term719 _70504 _70508.
Proof. exact (conj (@lem5442442) (@lem5442303 _70505 _70506 _70507 _70504 _70508 h1)). Qed.
Lemma lem5442445 (x : real) (y : real) : term714 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5442446 (_70504 : int) (_70508 : int) : term720 _70504 _70508.
Proof. exact (@lem5442445 term227 (term363 _70504 _70508)). Qed.
Lemma lem5442447 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) (h1 : term644 _70505 _70506 _70507 _70504 _70508) : term721 _70504 _70508.
Proof. exact (@lem5442446 _70504 _70508 (@lem5442443 _70505 _70506 _70507 _70504 _70508 h1)). Qed.
Lemma lem5442448 (_70504 : int) (_70508 : int) : (term722 _70504 _70508) = (term363 _70504 _70508).
Proof. exact (@lem1982733 (term363 _70504 _70508)). Qed.
Lemma lem5442449 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5442450 (_70504 : int) (_70508 : int) : (term723 _70504 _70508) = (term365 _70504 _70508).
Proof. exact (MK_COMB (@lem5442449) (@lem5442448 _70504 _70508)). Qed.
Lemma lem5442451 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5442452 (_70504 : int) (_70508 : int) : (term721 _70504 _70508) = (term366 _70504 _70508).
Proof. exact (MK_COMB (@lem5442450 _70504 _70508) (@lem5442451)). Qed.
Lemma lem5442453 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) (h1 : term644 _70505 _70506 _70507 _70504 _70508) : term366 _70504 _70508.
Proof. exact (EQ_MP (@lem5442452 _70504 _70508) (@lem5442447 _70505 _70506 _70507 _70504 _70508 h1)). Qed.
Lemma lem5442454 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) (h1 : term644 _70505 _70506 _70507 _70504 _70508) : term724 _70504 _70508.
Proof. exact (conj (@lem5442453 _70505 _70506 _70507 _70504 _70508 h1) (@lem5442379 _70505 _70506 _70507 _70504 _70508 h1)). Qed.
Lemma lem5442456 (x : real) (y : real) : term725 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5442457 (_70504 : int) (_70508 : int) : term726 _70504 _70508.
Proof. exact (@lem5442456 (term363 _70504 _70508) (term331 _70504 _70508)). Qed.
Lemma lem5442458 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) (h1 : term644 _70505 _70506 _70507 _70504 _70508) : term727 _70504 _70508.
Proof. exact (@lem5442457 _70504 _70508 (@lem5442454 _70505 _70506 _70507 _70504 _70508 h1)). Qed.
Lemma lem5442459 (_70504 : int) (_70508 : int) : (term728 _70504 _70508) = (term729 _70504 _70508).
Proof. exact (@lem1982753 (term336 _70504) (real_of_int _70504) (real_of_int _70508) (term330 _70508)). Qed.
Lemma lem5442460 (_70504 : int) : (term730 _70504) = (term731 _70504).
Proof. exact (@lem1982713 term294 (real_of_int _70504)). Qed.
Lemma lem5442462 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5442463 : term227 = term320.
Proof. exact (@lem5442462 term228). Qed.
Lemma lem5442465 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5442466 : term294 = term295.
Proof. exact (@lem5442465 term228). Qed.
Lemma lem5442467 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5442468 : term732 = term733.
Proof. exact (MK_COMB (@lem5442467) (@lem5442466)). Qed.
Lemma lem5442469 : term734 = term735.
Proof. exact (MK_COMB (@lem5442468) (@lem5442463)). Qed.
Lemma lem5442470 : term736.
Proof. exact (@lem1981473 term294 term227 term227 term227 term214 term227). Qed.
Lemma lem5442472 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442473 : term700 = term706.
Proof. exact (@lem5442472 (NUMERAL 0) term228). Qed.
Lemma lem5442474 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442475 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442476 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442475 h1) (fun h1 : term706 = True => @lem5442474)). Qed.
Lemma lem5442477 : term706 = True.
Proof. exact (EQ_MP (@lem5442476) (@lem5442474)). Qed.
Lemma lem5442478 : term700 = True.
Proof. exact (TRANS (@lem5442473) (@lem5442477)). Qed.
Lemma lem5442479 : True = term700.
Proof. exact (SYM (@lem5442478)). Qed.
Lemma lem5442480 : term700.
Proof. exact (EQ_MP (@lem5442479) (@lem0)). Qed.
Lemma lem5442481 : term737.
Proof. exact (@lem5442470 (@lem5442480)). Qed.
Lemma lem5442483 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442484 : term700 = term706.
Proof. exact (@lem5442483 (NUMERAL 0) term228). Qed.
Lemma lem5442485 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442486 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442487 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442486 h1) (fun h1 : term706 = True => @lem5442485)). Qed.
Lemma lem5442488 : term706 = True.
Proof. exact (EQ_MP (@lem5442487) (@lem5442485)). Qed.
Lemma lem5442489 : term700 = True.
Proof. exact (TRANS (@lem5442484) (@lem5442488)). Qed.
Lemma lem5442490 : True = term700.
Proof. exact (SYM (@lem5442489)). Qed.
Lemma lem5442491 : term700.
Proof. exact (EQ_MP (@lem5442490) (@lem0)). Qed.
Lemma lem5442492 : term738.
Proof. exact (@lem5442481 (@lem5442491)). Qed.
Lemma lem5442494 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442495 : term700 = term706.
Proof. exact (@lem5442494 (NUMERAL 0) term228). Qed.
Lemma lem5442496 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442497 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442498 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442497 h1) (fun h1 : term706 = True => @lem5442496)). Qed.
Lemma lem5442499 : term706 = True.
Proof. exact (EQ_MP (@lem5442498) (@lem5442496)). Qed.
Lemma lem5442500 : term700 = True.
Proof. exact (TRANS (@lem5442495) (@lem5442499)). Qed.
Lemma lem5442501 : True = term700.
Proof. exact (SYM (@lem5442500)). Qed.
Lemma lem5442502 : term700.
Proof. exact (EQ_MP (@lem5442501) (@lem0)). Qed.
Lemma lem5442503 : term739.
Proof. exact (@lem5442492 (@lem5442502)). Qed.
Lemma lem5442505 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5442506 : term303 = term304.
Proof. exact (@lem5442505 term228 term228). Qed.
Lemma lem5442507 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5442508 : term306 = term228.
Proof. exact (EQ_MP (@lem5442507) (@lem940073)). Qed.
Lemma lem5442509 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5442510 : term304 = term227.
Proof. exact (MK_COMB (@lem5442509) (@lem5442508)). Qed.
Lemma lem5442511 : term303 = term227.
Proof. exact (TRANS (@lem5442506) (@lem5442510)). Qed.
Lemma lem5442513 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5442514 : term321 = term326.
Proof. exact (@lem5442513 term228 term228). Qed.
Lemma lem5442515 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5442516 : term306 = term228.
Proof. exact (EQ_MP (@lem5442515) (@lem940073)). Qed.
Lemma lem5442517 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5442518 : term304 = term227.
Proof. exact (MK_COMB (@lem5442517) (@lem5442516)). Qed.
Lemma lem5442519 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5442520 : term326 = term294.
Proof. exact (MK_COMB (@lem5442519) (@lem5442518)). Qed.
Lemma lem5442521 : term321 = term294.
Proof. exact (TRANS (@lem5442514) (@lem5442520)). Qed.
Lemma lem5442522 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5442523 : term740 = term732.
Proof. exact (MK_COMB (@lem5442522) (@lem5442521)). Qed.
Lemma lem5442524 : term741 = term734.
Proof. exact (MK_COMB (@lem5442523) (@lem5442511)). Qed.
Lemma lem5442526 (m : nat) : (term742 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5442527 : term734 = term214.
Proof. exact (@lem5442526 term228). Qed.
Lemma lem5442528 : term741 = term214.
Proof. exact (TRANS (@lem5442524) (@lem5442527)). Qed.
Lemma lem5442529 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5442530 : term743 = term744.
Proof. exact (MK_COMB (@lem5442529) (@lem5442528)). Qed.
Lemma lem5442531 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem5442532 : term745 = term711.
Proof. exact (MK_COMB (@lem5442530) (@lem5442531)). Qed.
Lemma lem5442534 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5442535 : term711 = term214.
Proof. exact (@lem5442534 term228). Qed.
Lemma lem5442536 : term745 = term214.
Proof. exact (TRANS (@lem5442532) (@lem5442535)). Qed.
Lemma lem5442538 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5442539 : term303 = term304.
Proof. exact (@lem5442538 term228 term228). Qed.
Lemma lem5442540 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5442541 : term306 = term228.
Proof. exact (EQ_MP (@lem5442540) (@lem940073)). Qed.
Lemma lem5442542 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5442543 : term304 = term227.
Proof. exact (MK_COMB (@lem5442542) (@lem5442541)). Qed.
Lemma lem5442544 : term303 = term227.
Proof. exact (TRANS (@lem5442539) (@lem5442543)). Qed.
Lemma lem5442545 : term744 = term744.
Proof. exact (eq_refl term744). Qed.
Lemma lem5442546 : term746 = term711.
Proof. exact (MK_COMB (@lem5442545) (@lem5442544)). Qed.
Lemma lem5442548 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5442549 : term711 = term214.
Proof. exact (@lem5442548 term228). Qed.
Lemma lem5442550 : term746 = term214.
Proof. exact (TRANS (@lem5442546) (@lem5442549)). Qed.
Lemma lem5442551 : term214 = term746.
Proof. exact (SYM (@lem5442550)). Qed.
Lemma lem5442552 : term745 = term746.
Proof. exact (TRANS (@lem5442536) (@lem5442551)). Qed.
Lemma lem5442553 : term735 = term291.
Proof. exact (@lem5442503 (@lem5442552)). Qed.
Lemma lem5442554 : term734 = term291.
Proof. exact (TRANS (@lem5442469) (@lem5442553)). Qed.
Lemma lem5442556 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5442557 : term291 = term214.
Proof. exact (@lem5442556 term214). Qed.
Lemma lem5442558 : term734 = term214.
Proof. exact (TRANS (@lem5442554) (@lem5442557)). Qed.
Lemma lem5442559 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5442560 : term747 = term744.
Proof. exact (MK_COMB (@lem5442559) (@lem5442558)). Qed.
Lemma lem5442561 (_70504 : int) : (real_of_int _70504) = (real_of_int _70504).
Proof. exact (eq_refl (real_of_int _70504)). Qed.
Lemma lem5442562 (_70504 : int) : (term731 _70504) = (term748 _70504).
Proof. exact (MK_COMB (@lem5442560) (@lem5442561 _70504)). Qed.
Lemma lem5442563 (_70504 : int) : (term730 _70504) = (term748 _70504).
Proof. exact (TRANS (@lem5442460 _70504) (@lem5442562 _70504)). Qed.
Lemma lem5442564 (_70504 : int) : (term748 _70504) = term214.
Proof. exact (@lem1982719 (real_of_int _70504)). Qed.
Lemma lem5442565 (_70504 : int) : (term730 _70504) = term214.
Proof. exact (TRANS (@lem5442563 _70504) (@lem5442564 _70504)). Qed.
Lemma lem5442566 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5442567 (_70504 : int) : (term749 _70504) = term750.
Proof. exact (MK_COMB (@lem5442566) (@lem5442565 _70504)). Qed.
Lemma lem5442568 (_70508 : int) : (term751 _70508) = (term752 _70508).
Proof. exact (@lem1982763 (real_of_int _70508) (term336 _70508) term294). Qed.
Lemma lem5442569 (_70508 : int) : (term753 _70508) = (term731 _70508).
Proof. exact (@lem1982715 term294 (real_of_int _70508)). Qed.
Lemma lem5442571 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5442572 : term227 = term320.
Proof. exact (@lem5442571 term228). Qed.
Lemma lem5442574 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5442575 : term294 = term295.
Proof. exact (@lem5442574 term228). Qed.
Lemma lem5442576 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5442577 : term732 = term733.
Proof. exact (MK_COMB (@lem5442576) (@lem5442575)). Qed.
Lemma lem5442578 : term734 = term735.
Proof. exact (MK_COMB (@lem5442577) (@lem5442572)). Qed.
Lemma lem5442579 : term736.
Proof. exact (@lem1981473 term294 term227 term227 term227 term214 term227). Qed.
Lemma lem5442581 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442582 : term700 = term706.
Proof. exact (@lem5442581 (NUMERAL 0) term228). Qed.
Lemma lem5442583 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442584 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442585 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442584 h1) (fun h1 : term706 = True => @lem5442583)). Qed.
Lemma lem5442586 : term706 = True.
Proof. exact (EQ_MP (@lem5442585) (@lem5442583)). Qed.
Lemma lem5442587 : term700 = True.
Proof. exact (TRANS (@lem5442582) (@lem5442586)). Qed.
Lemma lem5442588 : True = term700.
Proof. exact (SYM (@lem5442587)). Qed.
Lemma lem5442589 : term700.
Proof. exact (EQ_MP (@lem5442588) (@lem0)). Qed.
Lemma lem5442590 : term737.
Proof. exact (@lem5442579 (@lem5442589)). Qed.
Lemma lem5442592 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442593 : term700 = term706.
Proof. exact (@lem5442592 (NUMERAL 0) term228). Qed.
Lemma lem5442594 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442595 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442596 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442595 h1) (fun h1 : term706 = True => @lem5442594)). Qed.
Lemma lem5442597 : term706 = True.
Proof. exact (EQ_MP (@lem5442596) (@lem5442594)). Qed.
Lemma lem5442598 : term700 = True.
Proof. exact (TRANS (@lem5442593) (@lem5442597)). Qed.
Lemma lem5442599 : True = term700.
Proof. exact (SYM (@lem5442598)). Qed.
Lemma lem5442600 : term700.
Proof. exact (EQ_MP (@lem5442599) (@lem0)). Qed.
Lemma lem5442601 : term738.
Proof. exact (@lem5442590 (@lem5442600)). Qed.
Lemma lem5442603 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442604 : term700 = term706.
Proof. exact (@lem5442603 (NUMERAL 0) term228). Qed.
Lemma lem5442605 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442606 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442607 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442606 h1) (fun h1 : term706 = True => @lem5442605)). Qed.
Lemma lem5442608 : term706 = True.
Proof. exact (EQ_MP (@lem5442607) (@lem5442605)). Qed.
Lemma lem5442609 : term700 = True.
Proof. exact (TRANS (@lem5442604) (@lem5442608)). Qed.
Lemma lem5442610 : True = term700.
Proof. exact (SYM (@lem5442609)). Qed.
Lemma lem5442611 : term700.
Proof. exact (EQ_MP (@lem5442610) (@lem0)). Qed.
Lemma lem5442612 : term739.
Proof. exact (@lem5442601 (@lem5442611)). Qed.
Lemma lem5442614 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5442615 : term303 = term304.
Proof. exact (@lem5442614 term228 term228). Qed.
Lemma lem5442616 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5442617 : term306 = term228.
Proof. exact (EQ_MP (@lem5442616) (@lem940073)). Qed.
Lemma lem5442618 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5442619 : term304 = term227.
Proof. exact (MK_COMB (@lem5442618) (@lem5442617)). Qed.
Lemma lem5442620 : term303 = term227.
Proof. exact (TRANS (@lem5442615) (@lem5442619)). Qed.
Lemma lem5442622 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5442623 : term321 = term326.
Proof. exact (@lem5442622 term228 term228). Qed.
Lemma lem5442624 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5442625 : term306 = term228.
Proof. exact (EQ_MP (@lem5442624) (@lem940073)). Qed.
Lemma lem5442626 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5442627 : term304 = term227.
Proof. exact (MK_COMB (@lem5442626) (@lem5442625)). Qed.
Lemma lem5442628 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5442629 : term326 = term294.
Proof. exact (MK_COMB (@lem5442628) (@lem5442627)). Qed.
Lemma lem5442630 : term321 = term294.
Proof. exact (TRANS (@lem5442623) (@lem5442629)). Qed.
Lemma lem5442631 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5442632 : term740 = term732.
Proof. exact (MK_COMB (@lem5442631) (@lem5442630)). Qed.
Lemma lem5442633 : term741 = term734.
Proof. exact (MK_COMB (@lem5442632) (@lem5442620)). Qed.
Lemma lem5442635 (m : nat) : (term742 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5442636 : term734 = term214.
Proof. exact (@lem5442635 term228). Qed.
Lemma lem5442637 : term741 = term214.
Proof. exact (TRANS (@lem5442633) (@lem5442636)). Qed.
Lemma lem5442638 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5442639 : term743 = term744.
Proof. exact (MK_COMB (@lem5442638) (@lem5442637)). Qed.
Lemma lem5442640 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem5442641 : term745 = term711.
Proof. exact (MK_COMB (@lem5442639) (@lem5442640)). Qed.
Lemma lem5442643 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5442644 : term711 = term214.
Proof. exact (@lem5442643 term228). Qed.
Lemma lem5442645 : term745 = term214.
Proof. exact (TRANS (@lem5442641) (@lem5442644)). Qed.
Lemma lem5442647 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5442648 : term303 = term304.
Proof. exact (@lem5442647 term228 term228). Qed.
Lemma lem5442649 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5442650 : term306 = term228.
Proof. exact (EQ_MP (@lem5442649) (@lem940073)). Qed.
Lemma lem5442651 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5442652 : term304 = term227.
Proof. exact (MK_COMB (@lem5442651) (@lem5442650)). Qed.
Lemma lem5442653 : term303 = term227.
Proof. exact (TRANS (@lem5442648) (@lem5442652)). Qed.
Lemma lem5442654 : term744 = term744.
Proof. exact (eq_refl term744). Qed.
Lemma lem5442655 : term746 = term711.
Proof. exact (MK_COMB (@lem5442654) (@lem5442653)). Qed.
Lemma lem5442657 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5442658 : term711 = term214.
Proof. exact (@lem5442657 term228). Qed.
Lemma lem5442659 : term746 = term214.
Proof. exact (TRANS (@lem5442655) (@lem5442658)). Qed.
Lemma lem5442660 : term214 = term746.
Proof. exact (SYM (@lem5442659)). Qed.
Lemma lem5442661 : term745 = term746.
Proof. exact (TRANS (@lem5442645) (@lem5442660)). Qed.
Lemma lem5442662 : term735 = term291.
Proof. exact (@lem5442612 (@lem5442661)). Qed.
Lemma lem5442663 : term734 = term291.
Proof. exact (TRANS (@lem5442578) (@lem5442662)). Qed.
Lemma lem5442665 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5442666 : term291 = term214.
Proof. exact (@lem5442665 term214). Qed.
Lemma lem5442667 : term734 = term214.
Proof. exact (TRANS (@lem5442663) (@lem5442666)). Qed.
Lemma lem5442668 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5442669 : term747 = term744.
Proof. exact (MK_COMB (@lem5442668) (@lem5442667)). Qed.
Lemma lem5442670 (_70508 : int) : (real_of_int _70508) = (real_of_int _70508).
Proof. exact (eq_refl (real_of_int _70508)). Qed.
Lemma lem5442671 (_70508 : int) : (term731 _70508) = (term748 _70508).
Proof. exact (MK_COMB (@lem5442669) (@lem5442670 _70508)). Qed.
Lemma lem5442672 (_70508 : int) : (term753 _70508) = (term748 _70508).
Proof. exact (TRANS (@lem5442569 _70508) (@lem5442671 _70508)). Qed.
Lemma lem5442673 (_70508 : int) : (term748 _70508) = term214.
Proof. exact (@lem1982719 (real_of_int _70508)). Qed.
Lemma lem5442674 (_70508 : int) : (term753 _70508) = term214.
Proof. exact (TRANS (@lem5442672 _70508) (@lem5442673 _70508)). Qed.
Lemma lem5442675 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5442676 (_70508 : int) : (term754 _70508) = term750.
Proof. exact (MK_COMB (@lem5442675) (@lem5442674 _70508)). Qed.
Lemma lem5442677 : term294 = term294.
Proof. exact (eq_refl term294). Qed.
Lemma lem5442678 (_70508 : int) : (term752 _70508) = term755.
Proof. exact (MK_COMB (@lem5442676 _70508) (@lem5442677)). Qed.
Lemma lem5442679 (_70508 : int) : (term751 _70508) = term755.
Proof. exact (TRANS (@lem5442568 _70508) (@lem5442678 _70508)). Qed.
Lemma lem5442680 : term755 = term294.
Proof. exact (@lem1982721 term294). Qed.
Lemma lem5442681 (_70508 : int) : (term751 _70508) = term294.
Proof. exact (TRANS (@lem5442679 _70508) (@lem5442680)). Qed.
Lemma lem5442682 (_70504 : int) (_70508 : int) : (term729 _70504 _70508) = term755.
Proof. exact (MK_COMB (@lem5442567 _70504) (@lem5442681 _70508)). Qed.
Lemma lem5442683 (_70504 : int) (_70508 : int) : (term728 _70504 _70508) = term755.
Proof. exact (TRANS (@lem5442459 _70504 _70508) (@lem5442682 _70504 _70508)). Qed.
Lemma lem5442684 : term755 = term294.
Proof. exact (@lem1982721 term294). Qed.
Lemma lem5442685 (_70504 : int) (_70508 : int) : (term728 _70504 _70508) = term294.
Proof. exact (TRANS (@lem5442683 _70504 _70508) (@lem5442684)). Qed.
Lemma lem5442686 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5442687 (_70504 : int) (_70508 : int) : (term756 _70504 _70508) = term757.
Proof. exact (MK_COMB (@lem5442686) (@lem5442685 _70504 _70508)). Qed.
Lemma lem5442688 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5442689 (_70504 : int) (_70508 : int) : (term727 _70504 _70508) = term758.
Proof. exact (MK_COMB (@lem5442687 _70504 _70508) (@lem5442688)). Qed.
Lemma lem5442690 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) (h1 : term644 _70505 _70506 _70507 _70504 _70508) : term758.
Proof. exact (EQ_MP (@lem5442689 _70504 _70508) (@lem5442458 _70505 _70506 _70507 _70504 _70508 h1)). Qed.
Lemma lem5442692 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5442693 : term758 = term759.
Proof. exact (@lem5442692 term214 term294). Qed.
Lemma lem5442695 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5442696 : term294 = term295.
Proof. exact (@lem5442695 term228). Qed.
Lemma lem5442698 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5442699 : term214 = term291.
Proof. exact (@lem5442698 (NUMERAL 0)). Qed.
Lemma lem5442700 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5442701 : term216 = term760.
Proof. exact (MK_COMB (@lem5442700) (@lem5442699)). Qed.
Lemma lem5442702 : term759 = term761.
Proof. exact (MK_COMB (@lem5442701) (@lem5442696)). Qed.
Lemma lem5442703 : term762.
Proof. exact (@lem1980026 term214 term227 term294 term227). Qed.
Lemma lem5442705 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442706 : term700 = term706.
Proof. exact (@lem5442705 (NUMERAL 0) term228). Qed.
Lemma lem5442707 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442708 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442709 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442708 h1) (fun h1 : term706 = True => @lem5442707)). Qed.
Lemma lem5442710 : term706 = True.
Proof. exact (EQ_MP (@lem5442709) (@lem5442707)). Qed.
Lemma lem5442711 : term700 = True.
Proof. exact (TRANS (@lem5442706) (@lem5442710)). Qed.
Lemma lem5442712 : True = term700.
Proof. exact (SYM (@lem5442711)). Qed.
Lemma lem5442713 : term700.
Proof. exact (EQ_MP (@lem5442712) (@lem0)). Qed.
Lemma lem5442714 : term763.
Proof. exact (@lem5442703 (@lem5442713)). Qed.
Lemma lem5442716 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442717 : term700 = term706.
Proof. exact (@lem5442716 (NUMERAL 0) term228). Qed.
Lemma lem5442718 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442719 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442720 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442719 h1) (fun h1 : term706 = True => @lem5442718)). Qed.
Lemma lem5442721 : term706 = True.
Proof. exact (EQ_MP (@lem5442720) (@lem5442718)). Qed.
Lemma lem5442722 : term700 = True.
Proof. exact (TRANS (@lem5442717) (@lem5442721)). Qed.
Lemma lem5442723 : True = term700.
Proof. exact (SYM (@lem5442722)). Qed.
Lemma lem5442724 : term700.
Proof. exact (EQ_MP (@lem5442723) (@lem0)). Qed.
Lemma lem5442725 : term761 = term764.
Proof. exact (@lem5442714 (@lem5442724)). Qed.
Lemma lem5442727 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5442728 : term321 = term326.
Proof. exact (@lem5442727 term228 term228). Qed.
Lemma lem5442729 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5442730 : term306 = term228.
Proof. exact (EQ_MP (@lem5442729) (@lem940073)). Qed.
Lemma lem5442731 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5442732 : term304 = term227.
Proof. exact (MK_COMB (@lem5442731) (@lem5442730)). Qed.
Lemma lem5442733 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5442734 : term326 = term294.
Proof. exact (MK_COMB (@lem5442733) (@lem5442732)). Qed.
Lemma lem5442735 : term321 = term294.
Proof. exact (TRANS (@lem5442728) (@lem5442734)). Qed.
Lemma lem5442737 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5442738 : term711 = term214.
Proof. exact (@lem5442737 term228). Qed.
Lemma lem5442739 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5442740 : term765 = term216.
Proof. exact (MK_COMB (@lem5442739) (@lem5442738)). Qed.
Lemma lem5442741 : term764 = term759.
Proof. exact (MK_COMB (@lem5442740) (@lem5442735)). Qed.
Lemma lem5442743 (m : nat) (n : nat) : (term766 m n) = (term767 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5442744 : term759 = term768.
Proof. exact (@lem5442743 (NUMERAL 0) term228). Qed.
Lemma lem5442745 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442746 (h1 : term707 = (BIT1 0)) : (term228 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5442747 : (term707 = (BIT1 0)) = ((term228 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442746 h1) (fun h1 : (term228 = (NUMERAL 0)) = False => @lem5442745)). Qed.
Lemma lem5442748 : (term228 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5442747) (@lem5442745)). Qed.
Lemma lem5442749 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5442750 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5442751 : term769 = (and True).
Proof. exact (MK_COMB (@lem5442750) (@lem5442749)). Qed.
Lemma lem5442752 : term768 = (True /\ False).
Proof. exact (MK_COMB (@lem5442751) (@lem5442748)). Qed.
Lemma lem5442754 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5442755 : term768 = False.
Proof. exact (TRANS (@lem5442752) (@lem5442754)). Qed.
Lemma lem5442756 : term759 = False.
Proof. exact (TRANS (@lem5442744) (@lem5442755)). Qed.
Lemma lem5442757 : term764 = False.
Proof. exact (TRANS (@lem5442741) (@lem5442756)). Qed.
Lemma lem5442758 : term761 = False.
Proof. exact (TRANS (@lem5442725) (@lem5442757)). Qed.
Lemma lem5442759 : term759 = False.
Proof. exact (TRANS (@lem5442702) (@lem5442758)). Qed.
Lemma lem5442760 : term758 = False.
Proof. exact (TRANS (@lem5442693) (@lem5442759)). Qed.
Lemma lem5442761 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) (h1 : term644 _70505 _70506 _70507 _70504 _70508) : False.
Proof. exact (EQ_MP (@lem5442760) (@lem5442690 _70505 _70506 _70507 _70504 _70508 h1)). Qed.
Lemma lem5442762 (_70505 : int) (_70506 : int) (_70507 : int) (_70504 : int) (_70508 : int) (h1 : term646 _70505 _70506 _70507 _70504 _70508) : False.
Proof. exact (or_elim (@lem5441807 _70505 _70506 _70507 _70504 _70508 h1) (fun h0 : term626 _70504 _70505 _70507 _70506 _70508 => @lem5442284 _70504 _70505 _70507 _70506 _70508 h0) (fun h0 : term644 _70505 _70506 _70507 _70504 _70508 => @lem5442761 _70505 _70506 _70507 _70504 _70508 h0)). Qed.
Lemma lem5442763 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term693 _70504 _70505 _70506 _70507 _70508) : term693 _70504 _70505 _70506 _70507 _70508.
Proof. exact (h1). Qed.
Lemma lem5442764 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) (h1 : term679 _70504 _70506 _70507 _70505 _70508) : term679 _70504 _70506 _70507 _70505 _70508.
Proof. exact (h1). Qed.
Lemma lem5442765 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) (h1 : term679 _70504 _70506 _70507 _70505 _70508) : term678 _70504 _70506 _70507 _70505 _70508.
Proof. exact (proj2 (@lem5442764 _70504 _70506 _70507 _70505 _70508 h1)). Qed.
Lemma lem5442767 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) (h1 : term679 _70504 _70506 _70507 _70505 _70508) : term677 _70504 _70506 _70507 _70505 _70508.
Proof. exact (proj2 (@lem5442765 _70504 _70506 _70507 _70505 _70508 h1)). Qed.
Lemma lem5442769 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) (h1 : term679 _70504 _70506 _70507 _70505 _70508) : term675 _70504 _70506 _70507 _70505 _70508.
Proof. exact (proj2 (@lem5442767 _70504 _70506 _70507 _70505 _70508 h1)). Qed.
Lemma lem5442771 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) (h1 : term679 _70504 _70506 _70507 _70505 _70508) : term673 _70504 _70506 _70507 _70505 _70508.
Proof. exact (proj2 (@lem5442769 _70504 _70506 _70507 _70505 _70508 h1)). Qed.
Lemma lem5442773 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) (h1 : term679 _70504 _70506 _70507 _70505 _70508) : term671 _70504 _70506 _70507 _70505 _70508.
Proof. exact (proj2 (@lem5442771 _70504 _70506 _70507 _70505 _70508 h1)). Qed.
Lemma lem5442775 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) (h1 : term679 _70504 _70506 _70507 _70505 _70508) : term669 _70504 _70506 _70507 _70505 _70508.
Proof. exact (proj2 (@lem5442773 _70504 _70506 _70507 _70505 _70508 h1)). Qed.
Lemma lem5442777 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) (h1 : term679 _70504 _70506 _70507 _70505 _70508) : term338 _70505 _70508.
Proof. exact (proj2 (@lem5442775 _70504 _70506 _70507 _70505 _70508 h1)). Qed.
Lemma lem5442778 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) (h1 : term679 _70504 _70506 _70507 _70505 _70508) : term372 _70504 _70505 _70506 _70507 _70508.
Proof. exact (proj1 (@lem5442775 _70504 _70506 _70507 _70505 _70508 h1)). Qed.
Lemma lem5442780 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) (h1 : term679 _70504 _70506 _70507 _70505 _70508) : term370 _70504 _70505 _70508.
Proof. exact (proj1 (@lem5442778 _70504 _70506 _70507 _70505 _70508 h1)). Qed.
Lemma lem5442781 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) (h1 : term679 _70504 _70506 _70507 _70505 _70508) : term368 _70505 _70508.
Proof. exact (proj2 (@lem5442780 _70504 _70506 _70507 _70505 _70508 h1)). Qed.
Lemma lem5442786 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5442787 : term699 = term700.
Proof. exact (@lem5442786 term214 term227). Qed.
Lemma lem5442789 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5442790 : term227 = term320.
Proof. exact (@lem5442789 term228). Qed.
Lemma lem5442792 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5442793 : term214 = term291.
Proof. exact (@lem5442792 (NUMERAL 0)). Qed.
Lemma lem5442794 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5442795 : term701 = term702.
Proof. exact (MK_COMB (@lem5442794) (@lem5442793)). Qed.
Lemma lem5442796 : term700 = term703.
Proof. exact (MK_COMB (@lem5442795) (@lem5442790)). Qed.
Lemma lem5442797 : term704.
Proof. exact (@lem1980255 term214 term227 term227 term227). Qed.
Lemma lem5442799 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442800 : term700 = term706.
Proof. exact (@lem5442799 (NUMERAL 0) term228). Qed.
Lemma lem5442801 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442802 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442803 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442802 h1) (fun h1 : term706 = True => @lem5442801)). Qed.
Lemma lem5442804 : term706 = True.
Proof. exact (EQ_MP (@lem5442803) (@lem5442801)). Qed.
Lemma lem5442805 : term700 = True.
Proof. exact (TRANS (@lem5442800) (@lem5442804)). Qed.
Lemma lem5442806 : True = term700.
Proof. exact (SYM (@lem5442805)). Qed.
Lemma lem5442807 : term700.
Proof. exact (EQ_MP (@lem5442806) (@lem0)). Qed.
Lemma lem5442808 : term708.
Proof. exact (@lem5442797 (@lem5442807)). Qed.
Lemma lem5442810 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442811 : term700 = term706.
Proof. exact (@lem5442810 (NUMERAL 0) term228). Qed.
Lemma lem5442812 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442813 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442814 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442813 h1) (fun h1 : term706 = True => @lem5442812)). Qed.
Lemma lem5442815 : term706 = True.
Proof. exact (EQ_MP (@lem5442814) (@lem5442812)). Qed.
Lemma lem5442816 : term700 = True.
Proof. exact (TRANS (@lem5442811) (@lem5442815)). Qed.
Lemma lem5442817 : True = term700.
Proof. exact (SYM (@lem5442816)). Qed.
Lemma lem5442818 : term700.
Proof. exact (EQ_MP (@lem5442817) (@lem0)). Qed.
Lemma lem5442819 : term703 = term709.
Proof. exact (@lem5442808 (@lem5442818)). Qed.
Lemma lem5442821 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5442822 : term303 = term304.
Proof. exact (@lem5442821 term228 term228). Qed.
Lemma lem5442823 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5442824 : term306 = term228.
Proof. exact (EQ_MP (@lem5442823) (@lem940073)). Qed.
Lemma lem5442825 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5442826 : term304 = term227.
Proof. exact (MK_COMB (@lem5442825) (@lem5442824)). Qed.
Lemma lem5442827 : term303 = term227.
Proof. exact (TRANS (@lem5442822) (@lem5442826)). Qed.
Lemma lem5442829 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5442830 : term711 = term214.
Proof. exact (@lem5442829 term228). Qed.
Lemma lem5442831 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5442832 : term712 = term701.
Proof. exact (MK_COMB (@lem5442831) (@lem5442830)). Qed.
Lemma lem5442833 : term709 = term700.
Proof. exact (MK_COMB (@lem5442832) (@lem5442827)). Qed.
Lemma lem5442835 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442836 : term700 = term706.
Proof. exact (@lem5442835 (NUMERAL 0) term228). Qed.
Lemma lem5442837 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442838 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442839 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442838 h1) (fun h1 : term706 = True => @lem5442837)). Qed.
Lemma lem5442840 : term706 = True.
Proof. exact (EQ_MP (@lem5442839) (@lem5442837)). Qed.
Lemma lem5442841 : term700 = True.
Proof. exact (TRANS (@lem5442836) (@lem5442840)). Qed.
Lemma lem5442842 : term709 = True.
Proof. exact (TRANS (@lem5442833) (@lem5442841)). Qed.
Lemma lem5442843 : term703 = True.
Proof. exact (TRANS (@lem5442819) (@lem5442842)). Qed.
Lemma lem5442844 : term700 = True.
Proof. exact (TRANS (@lem5442796) (@lem5442843)). Qed.
Lemma lem5442845 : term699 = True.
Proof. exact (TRANS (@lem5442787) (@lem5442844)). Qed.
Lemma lem5442846 : True = term699.
Proof. exact (SYM (@lem5442845)). Qed.
Lemma lem5442847 : term699.
Proof. exact (EQ_MP (@lem5442846) (@lem0)). Qed.
Lemma lem5442848 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) (h1 : term679 _70504 _70506 _70507 _70505 _70508) : term770 _70505 _70508.
Proof. exact (conj (@lem5442847) (@lem5442781 _70504 _70506 _70507 _70505 _70508 h1)). Qed.
Lemma lem5442850 (x : real) (y : real) : term714 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5442851 (_70505 : int) (_70508 : int) : term771 _70505 _70508.
Proof. exact (@lem5442850 term227 (term362 _70505 _70508)). Qed.
Lemma lem5442852 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) (h1 : term679 _70504 _70506 _70507 _70505 _70508) : term772 _70505 _70508.
Proof. exact (@lem5442851 _70505 _70508 (@lem5442848 _70504 _70506 _70507 _70505 _70508 h1)). Qed.
Lemma lem5442853 (_70505 : int) (_70508 : int) : (term773 _70505 _70508) = (term362 _70505 _70508).
Proof. exact (@lem1982733 (term362 _70505 _70508)). Qed.
Lemma lem5442854 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5442855 (_70505 : int) (_70508 : int) : (term774 _70505 _70508) = (term367 _70505 _70508).
Proof. exact (MK_COMB (@lem5442854) (@lem5442853 _70505 _70508)). Qed.
Lemma lem5442856 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5442857 (_70505 : int) (_70508 : int) : (term772 _70505 _70508) = (term368 _70505 _70508).
Proof. exact (MK_COMB (@lem5442855 _70505 _70508) (@lem5442856)). Qed.
Lemma lem5442858 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) (h1 : term679 _70504 _70506 _70507 _70505 _70508) : term368 _70505 _70508.
Proof. exact (EQ_MP (@lem5442857 _70505 _70508) (@lem5442852 _70504 _70506 _70507 _70505 _70508 h1)). Qed.
Lemma lem5442860 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5442861 : term699 = term700.
Proof. exact (@lem5442860 term214 term227). Qed.
Lemma lem5442863 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5442864 : term227 = term320.
Proof. exact (@lem5442863 term228). Qed.
Lemma lem5442866 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5442867 : term214 = term291.
Proof. exact (@lem5442866 (NUMERAL 0)). Qed.
Lemma lem5442868 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5442869 : term701 = term702.
Proof. exact (MK_COMB (@lem5442868) (@lem5442867)). Qed.
Lemma lem5442870 : term700 = term703.
Proof. exact (MK_COMB (@lem5442869) (@lem5442864)). Qed.
Lemma lem5442871 : term704.
Proof. exact (@lem1980255 term214 term227 term227 term227). Qed.
Lemma lem5442873 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442874 : term700 = term706.
Proof. exact (@lem5442873 (NUMERAL 0) term228). Qed.
Lemma lem5442875 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442876 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442877 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442876 h1) (fun h1 : term706 = True => @lem5442875)). Qed.
Lemma lem5442878 : term706 = True.
Proof. exact (EQ_MP (@lem5442877) (@lem5442875)). Qed.
Lemma lem5442879 : term700 = True.
Proof. exact (TRANS (@lem5442874) (@lem5442878)). Qed.
Lemma lem5442880 : True = term700.
Proof. exact (SYM (@lem5442879)). Qed.
Lemma lem5442881 : term700.
Proof. exact (EQ_MP (@lem5442880) (@lem0)). Qed.
Lemma lem5442882 : term708.
Proof. exact (@lem5442871 (@lem5442881)). Qed.
Lemma lem5442884 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442885 : term700 = term706.
Proof. exact (@lem5442884 (NUMERAL 0) term228). Qed.
Lemma lem5442886 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442887 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442888 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442887 h1) (fun h1 : term706 = True => @lem5442886)). Qed.
Lemma lem5442889 : term706 = True.
Proof. exact (EQ_MP (@lem5442888) (@lem5442886)). Qed.
Lemma lem5442890 : term700 = True.
Proof. exact (TRANS (@lem5442885) (@lem5442889)). Qed.
Lemma lem5442891 : True = term700.
Proof. exact (SYM (@lem5442890)). Qed.
Lemma lem5442892 : term700.
Proof. exact (EQ_MP (@lem5442891) (@lem0)). Qed.
Lemma lem5442893 : term703 = term709.
Proof. exact (@lem5442882 (@lem5442892)). Qed.
Lemma lem5442895 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5442896 : term303 = term304.
Proof. exact (@lem5442895 term228 term228). Qed.
Lemma lem5442897 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5442898 : term306 = term228.
Proof. exact (EQ_MP (@lem5442897) (@lem940073)). Qed.
Lemma lem5442899 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5442900 : term304 = term227.
Proof. exact (MK_COMB (@lem5442899) (@lem5442898)). Qed.
Lemma lem5442901 : term303 = term227.
Proof. exact (TRANS (@lem5442896) (@lem5442900)). Qed.
Lemma lem5442903 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5442904 : term711 = term214.
Proof. exact (@lem5442903 term228). Qed.
Lemma lem5442905 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5442906 : term712 = term701.
Proof. exact (MK_COMB (@lem5442905) (@lem5442904)). Qed.
Lemma lem5442907 : term709 = term700.
Proof. exact (MK_COMB (@lem5442906) (@lem5442901)). Qed.
Lemma lem5442909 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442910 : term700 = term706.
Proof. exact (@lem5442909 (NUMERAL 0) term228). Qed.
Lemma lem5442911 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442912 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442913 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442912 h1) (fun h1 : term706 = True => @lem5442911)). Qed.
Lemma lem5442914 : term706 = True.
Proof. exact (EQ_MP (@lem5442913) (@lem5442911)). Qed.
Lemma lem5442915 : term700 = True.
Proof. exact (TRANS (@lem5442910) (@lem5442914)). Qed.
Lemma lem5442916 : term709 = True.
Proof. exact (TRANS (@lem5442907) (@lem5442915)). Qed.
Lemma lem5442917 : term703 = True.
Proof. exact (TRANS (@lem5442893) (@lem5442916)). Qed.
Lemma lem5442918 : term700 = True.
Proof. exact (TRANS (@lem5442870) (@lem5442917)). Qed.
Lemma lem5442919 : term699 = True.
Proof. exact (TRANS (@lem5442861) (@lem5442918)). Qed.
Lemma lem5442920 : True = term699.
Proof. exact (SYM (@lem5442919)). Qed.
Lemma lem5442921 : term699.
Proof. exact (EQ_MP (@lem5442920) (@lem0)). Qed.
Lemma lem5442922 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) (h1 : term679 _70504 _70506 _70507 _70505 _70508) : term775 _70505 _70508.
Proof. exact (conj (@lem5442921) (@lem5442777 _70504 _70506 _70507 _70505 _70508 h1)). Qed.
Lemma lem5442924 (x : real) (y : real) : term714 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5442925 (_70505 : int) (_70508 : int) : term776 _70505 _70508.
Proof. exact (@lem5442924 term227 (term335 _70505 _70508)). Qed.
Lemma lem5442926 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) (h1 : term679 _70504 _70506 _70507 _70505 _70508) : term777 _70505 _70508.
Proof. exact (@lem5442925 _70505 _70508 (@lem5442922 _70504 _70506 _70507 _70505 _70508 h1)). Qed.
Lemma lem5442927 (_70505 : int) (_70508 : int) : (term778 _70505 _70508) = (term335 _70505 _70508).
Proof. exact (@lem1982733 (term335 _70505 _70508)). Qed.
Lemma lem5442928 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5442929 (_70505 : int) (_70508 : int) : (term779 _70505 _70508) = (term337 _70505 _70508).
Proof. exact (MK_COMB (@lem5442928) (@lem5442927 _70505 _70508)). Qed.
Lemma lem5442930 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5442931 (_70505 : int) (_70508 : int) : (term777 _70505 _70508) = (term338 _70505 _70508).
Proof. exact (MK_COMB (@lem5442929 _70505 _70508) (@lem5442930)). Qed.
Lemma lem5442932 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) (h1 : term679 _70504 _70506 _70507 _70505 _70508) : term338 _70505 _70508.
Proof. exact (EQ_MP (@lem5442931 _70505 _70508) (@lem5442926 _70504 _70506 _70507 _70505 _70508 h1)). Qed.
Lemma lem5442933 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) (h1 : term679 _70504 _70506 _70507 _70505 _70508) : term780 _70505 _70508.
Proof. exact (conj (@lem5442932 _70504 _70506 _70507 _70505 _70508 h1) (@lem5442858 _70504 _70506 _70507 _70505 _70508 h1)). Qed.
Lemma lem5442935 (x : real) (y : real) : term725 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5442936 (_70505 : int) (_70508 : int) : term781 _70505 _70508.
Proof. exact (@lem5442935 (term335 _70505 _70508) (term362 _70505 _70508)). Qed.
Lemma lem5442937 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) (h1 : term679 _70504 _70506 _70507 _70505 _70508) : term782 _70505 _70508.
Proof. exact (@lem5442936 _70505 _70508 (@lem5442933 _70504 _70506 _70507 _70505 _70508 h1)). Qed.
Lemma lem5442938 (_70505 : int) (_70508 : int) : (term783 _70505 _70508) = (term784 _70505 _70508).
Proof. exact (@lem1982753 (term336 _70505) (real_of_int _70505) (term785 _70508) (term336 _70508)). Qed.
Lemma lem5442939 (_70505 : int) : (term730 _70505) = (term731 _70505).
Proof. exact (@lem1982713 term294 (real_of_int _70505)). Qed.
Lemma lem5442941 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5442942 : term227 = term320.
Proof. exact (@lem5442941 term228). Qed.
Lemma lem5442944 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5442945 : term294 = term295.
Proof. exact (@lem5442944 term228). Qed.
Lemma lem5442946 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5442947 : term732 = term733.
Proof. exact (MK_COMB (@lem5442946) (@lem5442945)). Qed.
Lemma lem5442948 : term734 = term735.
Proof. exact (MK_COMB (@lem5442947) (@lem5442942)). Qed.
Lemma lem5442949 : term736.
Proof. exact (@lem1981473 term294 term227 term227 term227 term214 term227). Qed.
Lemma lem5442951 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442952 : term700 = term706.
Proof. exact (@lem5442951 (NUMERAL 0) term228). Qed.
Lemma lem5442953 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442954 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442955 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442954 h1) (fun h1 : term706 = True => @lem5442953)). Qed.
Lemma lem5442956 : term706 = True.
Proof. exact (EQ_MP (@lem5442955) (@lem5442953)). Qed.
Lemma lem5442957 : term700 = True.
Proof. exact (TRANS (@lem5442952) (@lem5442956)). Qed.
Lemma lem5442958 : True = term700.
Proof. exact (SYM (@lem5442957)). Qed.
Lemma lem5442959 : term700.
Proof. exact (EQ_MP (@lem5442958) (@lem0)). Qed.
Lemma lem5442960 : term737.
Proof. exact (@lem5442949 (@lem5442959)). Qed.
Lemma lem5442962 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442963 : term700 = term706.
Proof. exact (@lem5442962 (NUMERAL 0) term228). Qed.
Lemma lem5442964 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442965 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442966 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442965 h1) (fun h1 : term706 = True => @lem5442964)). Qed.
Lemma lem5442967 : term706 = True.
Proof. exact (EQ_MP (@lem5442966) (@lem5442964)). Qed.
Lemma lem5442968 : term700 = True.
Proof. exact (TRANS (@lem5442963) (@lem5442967)). Qed.
Lemma lem5442969 : True = term700.
Proof. exact (SYM (@lem5442968)). Qed.
Lemma lem5442970 : term700.
Proof. exact (EQ_MP (@lem5442969) (@lem0)). Qed.
Lemma lem5442971 : term738.
Proof. exact (@lem5442960 (@lem5442970)). Qed.
Lemma lem5442973 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5442974 : term700 = term706.
Proof. exact (@lem5442973 (NUMERAL 0) term228). Qed.
Lemma lem5442975 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5442976 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5442977 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5442976 h1) (fun h1 : term706 = True => @lem5442975)). Qed.
Lemma lem5442978 : term706 = True.
Proof. exact (EQ_MP (@lem5442977) (@lem5442975)). Qed.
Lemma lem5442979 : term700 = True.
Proof. exact (TRANS (@lem5442974) (@lem5442978)). Qed.
Lemma lem5442980 : True = term700.
Proof. exact (SYM (@lem5442979)). Qed.
Lemma lem5442981 : term700.
Proof. exact (EQ_MP (@lem5442980) (@lem0)). Qed.
Lemma lem5442982 : term739.
Proof. exact (@lem5442971 (@lem5442981)). Qed.
Lemma lem5442984 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5442985 : term303 = term304.
Proof. exact (@lem5442984 term228 term228). Qed.
Lemma lem5442986 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5442987 : term306 = term228.
Proof. exact (EQ_MP (@lem5442986) (@lem940073)). Qed.
Lemma lem5442988 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5442989 : term304 = term227.
Proof. exact (MK_COMB (@lem5442988) (@lem5442987)). Qed.
Lemma lem5442990 : term303 = term227.
Proof. exact (TRANS (@lem5442985) (@lem5442989)). Qed.
Lemma lem5442992 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5442993 : term321 = term326.
Proof. exact (@lem5442992 term228 term228). Qed.
Lemma lem5442994 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5442995 : term306 = term228.
Proof. exact (EQ_MP (@lem5442994) (@lem940073)). Qed.
Lemma lem5442996 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5442997 : term304 = term227.
Proof. exact (MK_COMB (@lem5442996) (@lem5442995)). Qed.
Lemma lem5442998 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5442999 : term326 = term294.
Proof. exact (MK_COMB (@lem5442998) (@lem5442997)). Qed.
Lemma lem5443000 : term321 = term294.
Proof. exact (TRANS (@lem5442993) (@lem5442999)). Qed.
Lemma lem5443001 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5443002 : term740 = term732.
Proof. exact (MK_COMB (@lem5443001) (@lem5443000)). Qed.
Lemma lem5443003 : term741 = term734.
Proof. exact (MK_COMB (@lem5443002) (@lem5442990)). Qed.
Lemma lem5443005 (m : nat) : (term742 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5443006 : term734 = term214.
Proof. exact (@lem5443005 term228). Qed.
Lemma lem5443007 : term741 = term214.
Proof. exact (TRANS (@lem5443003) (@lem5443006)). Qed.
Lemma lem5443008 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5443009 : term743 = term744.
Proof. exact (MK_COMB (@lem5443008) (@lem5443007)). Qed.
Lemma lem5443010 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem5443011 : term745 = term711.
Proof. exact (MK_COMB (@lem5443009) (@lem5443010)). Qed.
Lemma lem5443013 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5443014 : term711 = term214.
Proof. exact (@lem5443013 term228). Qed.
Lemma lem5443015 : term745 = term214.
Proof. exact (TRANS (@lem5443011) (@lem5443014)). Qed.
Lemma lem5443017 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5443018 : term303 = term304.
Proof. exact (@lem5443017 term228 term228). Qed.
Lemma lem5443019 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5443020 : term306 = term228.
Proof. exact (EQ_MP (@lem5443019) (@lem940073)). Qed.
Lemma lem5443021 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5443022 : term304 = term227.
Proof. exact (MK_COMB (@lem5443021) (@lem5443020)). Qed.
Lemma lem5443023 : term303 = term227.
Proof. exact (TRANS (@lem5443018) (@lem5443022)). Qed.
Lemma lem5443024 : term744 = term744.
Proof. exact (eq_refl term744). Qed.
Lemma lem5443025 : term746 = term711.
Proof. exact (MK_COMB (@lem5443024) (@lem5443023)). Qed.
Lemma lem5443027 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5443028 : term711 = term214.
Proof. exact (@lem5443027 term228). Qed.
Lemma lem5443029 : term746 = term214.
Proof. exact (TRANS (@lem5443025) (@lem5443028)). Qed.
Lemma lem5443030 : term214 = term746.
Proof. exact (SYM (@lem5443029)). Qed.
Lemma lem5443031 : term745 = term746.
Proof. exact (TRANS (@lem5443015) (@lem5443030)). Qed.
Lemma lem5443032 : term735 = term291.
Proof. exact (@lem5442982 (@lem5443031)). Qed.
Lemma lem5443033 : term734 = term291.
Proof. exact (TRANS (@lem5442948) (@lem5443032)). Qed.
Lemma lem5443035 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5443036 : term291 = term214.
Proof. exact (@lem5443035 term214). Qed.
Lemma lem5443037 : term734 = term214.
Proof. exact (TRANS (@lem5443033) (@lem5443036)). Qed.
Lemma lem5443038 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5443039 : term747 = term744.
Proof. exact (MK_COMB (@lem5443038) (@lem5443037)). Qed.
Lemma lem5443040 (_70505 : int) : (real_of_int _70505) = (real_of_int _70505).
Proof. exact (eq_refl (real_of_int _70505)). Qed.
Lemma lem5443041 (_70505 : int) : (term731 _70505) = (term748 _70505).
Proof. exact (MK_COMB (@lem5443039) (@lem5443040 _70505)). Qed.
Lemma lem5443042 (_70505 : int) : (term730 _70505) = (term748 _70505).
Proof. exact (TRANS (@lem5442939 _70505) (@lem5443041 _70505)). Qed.
Lemma lem5443043 (_70505 : int) : (term748 _70505) = term214.
Proof. exact (@lem1982719 (real_of_int _70505)). Qed.
Lemma lem5443044 (_70505 : int) : (term730 _70505) = term214.
Proof. exact (TRANS (@lem5443042 _70505) (@lem5443043 _70505)). Qed.
Lemma lem5443045 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5443046 (_70505 : int) : (term749 _70505) = term750.
Proof. exact (MK_COMB (@lem5443045) (@lem5443044 _70505)). Qed.
Lemma lem5443047 (_70508 : int) : (term786 _70508) = (term752 _70508).
Proof. exact (@lem1982759 (real_of_int _70508) (term336 _70508) term294). Qed.
Lemma lem5443048 (_70508 : int) : (term753 _70508) = (term731 _70508).
Proof. exact (@lem1982715 term294 (real_of_int _70508)). Qed.
Lemma lem5443050 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5443051 : term227 = term320.
Proof. exact (@lem5443050 term228). Qed.
Lemma lem5443053 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5443054 : term294 = term295.
Proof. exact (@lem5443053 term228). Qed.
Lemma lem5443055 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5443056 : term732 = term733.
Proof. exact (MK_COMB (@lem5443055) (@lem5443054)). Qed.
Lemma lem5443057 : term734 = term735.
Proof. exact (MK_COMB (@lem5443056) (@lem5443051)). Qed.
Lemma lem5443058 : term736.
Proof. exact (@lem1981473 term294 term227 term227 term227 term214 term227). Qed.
Lemma lem5443060 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5443061 : term700 = term706.
Proof. exact (@lem5443060 (NUMERAL 0) term228). Qed.
Lemma lem5443062 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5443063 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5443064 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5443063 h1) (fun h1 : term706 = True => @lem5443062)). Qed.
Lemma lem5443065 : term706 = True.
Proof. exact (EQ_MP (@lem5443064) (@lem5443062)). Qed.
Lemma lem5443066 : term700 = True.
Proof. exact (TRANS (@lem5443061) (@lem5443065)). Qed.
Lemma lem5443067 : True = term700.
Proof. exact (SYM (@lem5443066)). Qed.
Lemma lem5443068 : term700.
Proof. exact (EQ_MP (@lem5443067) (@lem0)). Qed.
Lemma lem5443069 : term737.
Proof. exact (@lem5443058 (@lem5443068)). Qed.
Lemma lem5443071 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5443072 : term700 = term706.
Proof. exact (@lem5443071 (NUMERAL 0) term228). Qed.
Lemma lem5443073 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5443074 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5443075 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5443074 h1) (fun h1 : term706 = True => @lem5443073)). Qed.
Lemma lem5443076 : term706 = True.
Proof. exact (EQ_MP (@lem5443075) (@lem5443073)). Qed.
Lemma lem5443077 : term700 = True.
Proof. exact (TRANS (@lem5443072) (@lem5443076)). Qed.
Lemma lem5443078 : True = term700.
Proof. exact (SYM (@lem5443077)). Qed.
Lemma lem5443079 : term700.
Proof. exact (EQ_MP (@lem5443078) (@lem0)). Qed.
Lemma lem5443080 : term738.
Proof. exact (@lem5443069 (@lem5443079)). Qed.
Lemma lem5443082 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5443083 : term700 = term706.
Proof. exact (@lem5443082 (NUMERAL 0) term228). Qed.
Lemma lem5443084 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5443085 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5443086 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5443085 h1) (fun h1 : term706 = True => @lem5443084)). Qed.
Lemma lem5443087 : term706 = True.
Proof. exact (EQ_MP (@lem5443086) (@lem5443084)). Qed.
Lemma lem5443088 : term700 = True.
Proof. exact (TRANS (@lem5443083) (@lem5443087)). Qed.
Lemma lem5443089 : True = term700.
Proof. exact (SYM (@lem5443088)). Qed.
Lemma lem5443090 : term700.
Proof. exact (EQ_MP (@lem5443089) (@lem0)). Qed.
Lemma lem5443091 : term739.
Proof. exact (@lem5443080 (@lem5443090)). Qed.
Lemma lem5443093 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5443094 : term303 = term304.
Proof. exact (@lem5443093 term228 term228). Qed.
Lemma lem5443095 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5443096 : term306 = term228.
Proof. exact (EQ_MP (@lem5443095) (@lem940073)). Qed.
Lemma lem5443097 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5443098 : term304 = term227.
Proof. exact (MK_COMB (@lem5443097) (@lem5443096)). Qed.
Lemma lem5443099 : term303 = term227.
Proof. exact (TRANS (@lem5443094) (@lem5443098)). Qed.
Lemma lem5443101 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5443102 : term321 = term326.
Proof. exact (@lem5443101 term228 term228). Qed.
Lemma lem5443103 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5443104 : term306 = term228.
Proof. exact (EQ_MP (@lem5443103) (@lem940073)). Qed.
Lemma lem5443105 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5443106 : term304 = term227.
Proof. exact (MK_COMB (@lem5443105) (@lem5443104)). Qed.
Lemma lem5443107 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5443108 : term326 = term294.
Proof. exact (MK_COMB (@lem5443107) (@lem5443106)). Qed.
Lemma lem5443109 : term321 = term294.
Proof. exact (TRANS (@lem5443102) (@lem5443108)). Qed.
Lemma lem5443110 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5443111 : term740 = term732.
Proof. exact (MK_COMB (@lem5443110) (@lem5443109)). Qed.
Lemma lem5443112 : term741 = term734.
Proof. exact (MK_COMB (@lem5443111) (@lem5443099)). Qed.
Lemma lem5443114 (m : nat) : (term742 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5443115 : term734 = term214.
Proof. exact (@lem5443114 term228). Qed.
Lemma lem5443116 : term741 = term214.
Proof. exact (TRANS (@lem5443112) (@lem5443115)). Qed.
Lemma lem5443117 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5443118 : term743 = term744.
Proof. exact (MK_COMB (@lem5443117) (@lem5443116)). Qed.
Lemma lem5443119 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem5443120 : term745 = term711.
Proof. exact (MK_COMB (@lem5443118) (@lem5443119)). Qed.
Lemma lem5443122 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5443123 : term711 = term214.
Proof. exact (@lem5443122 term228). Qed.
Lemma lem5443124 : term745 = term214.
Proof. exact (TRANS (@lem5443120) (@lem5443123)). Qed.
Lemma lem5443126 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5443127 : term303 = term304.
Proof. exact (@lem5443126 term228 term228). Qed.
Lemma lem5443128 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5443129 : term306 = term228.
Proof. exact (EQ_MP (@lem5443128) (@lem940073)). Qed.
Lemma lem5443130 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5443131 : term304 = term227.
Proof. exact (MK_COMB (@lem5443130) (@lem5443129)). Qed.
Lemma lem5443132 : term303 = term227.
Proof. exact (TRANS (@lem5443127) (@lem5443131)). Qed.
Lemma lem5443133 : term744 = term744.
Proof. exact (eq_refl term744). Qed.
Lemma lem5443134 : term746 = term711.
Proof. exact (MK_COMB (@lem5443133) (@lem5443132)). Qed.
Lemma lem5443136 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5443137 : term711 = term214.
Proof. exact (@lem5443136 term228). Qed.
Lemma lem5443138 : term746 = term214.
Proof. exact (TRANS (@lem5443134) (@lem5443137)). Qed.
Lemma lem5443139 : term214 = term746.
Proof. exact (SYM (@lem5443138)). Qed.
Lemma lem5443140 : term745 = term746.
Proof. exact (TRANS (@lem5443124) (@lem5443139)). Qed.
Lemma lem5443141 : term735 = term291.
Proof. exact (@lem5443091 (@lem5443140)). Qed.
Lemma lem5443142 : term734 = term291.
Proof. exact (TRANS (@lem5443057) (@lem5443141)). Qed.
Lemma lem5443144 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5443145 : term291 = term214.
Proof. exact (@lem5443144 term214). Qed.
Lemma lem5443146 : term734 = term214.
Proof. exact (TRANS (@lem5443142) (@lem5443145)). Qed.
Lemma lem5443147 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5443148 : term747 = term744.
Proof. exact (MK_COMB (@lem5443147) (@lem5443146)). Qed.
Lemma lem5443149 (_70508 : int) : (real_of_int _70508) = (real_of_int _70508).
Proof. exact (eq_refl (real_of_int _70508)). Qed.
Lemma lem5443150 (_70508 : int) : (term731 _70508) = (term748 _70508).
Proof. exact (MK_COMB (@lem5443148) (@lem5443149 _70508)). Qed.
Lemma lem5443151 (_70508 : int) : (term753 _70508) = (term748 _70508).
Proof. exact (TRANS (@lem5443048 _70508) (@lem5443150 _70508)). Qed.
Lemma lem5443152 (_70508 : int) : (term748 _70508) = term214.
Proof. exact (@lem1982719 (real_of_int _70508)). Qed.
Lemma lem5443153 (_70508 : int) : (term753 _70508) = term214.
Proof. exact (TRANS (@lem5443151 _70508) (@lem5443152 _70508)). Qed.
Lemma lem5443154 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5443155 (_70508 : int) : (term754 _70508) = term750.
Proof. exact (MK_COMB (@lem5443154) (@lem5443153 _70508)). Qed.
Lemma lem5443156 : term294 = term294.
Proof. exact (eq_refl term294). Qed.
Lemma lem5443157 (_70508 : int) : (term752 _70508) = term755.
Proof. exact (MK_COMB (@lem5443155 _70508) (@lem5443156)). Qed.
Lemma lem5443158 (_70508 : int) : (term786 _70508) = term755.
Proof. exact (TRANS (@lem5443047 _70508) (@lem5443157 _70508)). Qed.
Lemma lem5443159 : term755 = term294.
Proof. exact (@lem1982721 term294). Qed.
Lemma lem5443160 (_70508 : int) : (term786 _70508) = term294.
Proof. exact (TRANS (@lem5443158 _70508) (@lem5443159)). Qed.
Lemma lem5443161 (_70505 : int) (_70508 : int) : (term784 _70505 _70508) = term755.
Proof. exact (MK_COMB (@lem5443046 _70505) (@lem5443160 _70508)). Qed.
Lemma lem5443162 (_70505 : int) (_70508 : int) : (term783 _70505 _70508) = term755.
Proof. exact (TRANS (@lem5442938 _70505 _70508) (@lem5443161 _70505 _70508)). Qed.
Lemma lem5443163 : term755 = term294.
Proof. exact (@lem1982721 term294). Qed.
Lemma lem5443164 (_70505 : int) (_70508 : int) : (term783 _70505 _70508) = term294.
Proof. exact (TRANS (@lem5443162 _70505 _70508) (@lem5443163)). Qed.
Lemma lem5443165 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5443166 (_70505 : int) (_70508 : int) : (term787 _70505 _70508) = term757.
Proof. exact (MK_COMB (@lem5443165) (@lem5443164 _70505 _70508)). Qed.
Lemma lem5443167 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5443168 (_70505 : int) (_70508 : int) : (term782 _70505 _70508) = term758.
Proof. exact (MK_COMB (@lem5443166 _70505 _70508) (@lem5443167)). Qed.
Lemma lem5443169 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) (h1 : term679 _70504 _70506 _70507 _70505 _70508) : term758.
Proof. exact (EQ_MP (@lem5443168 _70505 _70508) (@lem5442937 _70504 _70506 _70507 _70505 _70508 h1)). Qed.
Lemma lem5443171 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5443172 : term758 = term759.
Proof. exact (@lem5443171 term214 term294). Qed.
Lemma lem5443174 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5443175 : term294 = term295.
Proof. exact (@lem5443174 term228). Qed.
Lemma lem5443177 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5443178 : term214 = term291.
Proof. exact (@lem5443177 (NUMERAL 0)). Qed.
Lemma lem5443179 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5443180 : term216 = term760.
Proof. exact (MK_COMB (@lem5443179) (@lem5443178)). Qed.
Lemma lem5443181 : term759 = term761.
Proof. exact (MK_COMB (@lem5443180) (@lem5443175)). Qed.
Lemma lem5443182 : term762.
Proof. exact (@lem1980026 term214 term227 term294 term227). Qed.
Lemma lem5443184 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5443185 : term700 = term706.
Proof. exact (@lem5443184 (NUMERAL 0) term228). Qed.
Lemma lem5443186 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5443187 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5443188 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5443187 h1) (fun h1 : term706 = True => @lem5443186)). Qed.
Lemma lem5443189 : term706 = True.
Proof. exact (EQ_MP (@lem5443188) (@lem5443186)). Qed.
Lemma lem5443190 : term700 = True.
Proof. exact (TRANS (@lem5443185) (@lem5443189)). Qed.
Lemma lem5443191 : True = term700.
Proof. exact (SYM (@lem5443190)). Qed.
Lemma lem5443192 : term700.
Proof. exact (EQ_MP (@lem5443191) (@lem0)). Qed.
Lemma lem5443193 : term763.
Proof. exact (@lem5443182 (@lem5443192)). Qed.
Lemma lem5443195 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5443196 : term700 = term706.
Proof. exact (@lem5443195 (NUMERAL 0) term228). Qed.
Lemma lem5443197 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5443198 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5443199 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5443198 h1) (fun h1 : term706 = True => @lem5443197)). Qed.
Lemma lem5443200 : term706 = True.
Proof. exact (EQ_MP (@lem5443199) (@lem5443197)). Qed.
Lemma lem5443201 : term700 = True.
Proof. exact (TRANS (@lem5443196) (@lem5443200)). Qed.
Lemma lem5443202 : True = term700.
Proof. exact (SYM (@lem5443201)). Qed.
Lemma lem5443203 : term700.
Proof. exact (EQ_MP (@lem5443202) (@lem0)). Qed.
Lemma lem5443204 : term761 = term764.
Proof. exact (@lem5443193 (@lem5443203)). Qed.
Lemma lem5443206 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5443207 : term321 = term326.
Proof. exact (@lem5443206 term228 term228). Qed.
Lemma lem5443208 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5443209 : term306 = term228.
Proof. exact (EQ_MP (@lem5443208) (@lem940073)). Qed.
Lemma lem5443210 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5443211 : term304 = term227.
Proof. exact (MK_COMB (@lem5443210) (@lem5443209)). Qed.
Lemma lem5443212 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5443213 : term326 = term294.
Proof. exact (MK_COMB (@lem5443212) (@lem5443211)). Qed.
Lemma lem5443214 : term321 = term294.
Proof. exact (TRANS (@lem5443207) (@lem5443213)). Qed.
Lemma lem5443216 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5443217 : term711 = term214.
Proof. exact (@lem5443216 term228). Qed.
Lemma lem5443218 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5443219 : term765 = term216.
Proof. exact (MK_COMB (@lem5443218) (@lem5443217)). Qed.
Lemma lem5443220 : term764 = term759.
Proof. exact (MK_COMB (@lem5443219) (@lem5443214)). Qed.
Lemma lem5443222 (m : nat) (n : nat) : (term766 m n) = (term767 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5443223 : term759 = term768.
Proof. exact (@lem5443222 (NUMERAL 0) term228). Qed.
Lemma lem5443224 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5443225 (h1 : term707 = (BIT1 0)) : (term228 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5443226 : (term707 = (BIT1 0)) = ((term228 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5443225 h1) (fun h1 : (term228 = (NUMERAL 0)) = False => @lem5443224)). Qed.
Lemma lem5443227 : (term228 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5443226) (@lem5443224)). Qed.
Lemma lem5443228 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5443229 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5443230 : term769 = (and True).
Proof. exact (MK_COMB (@lem5443229) (@lem5443228)). Qed.
Lemma lem5443231 : term768 = (True /\ False).
Proof. exact (MK_COMB (@lem5443230) (@lem5443227)). Qed.
Lemma lem5443233 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5443234 : term768 = False.
Proof. exact (TRANS (@lem5443231) (@lem5443233)). Qed.
Lemma lem5443235 : term759 = False.
Proof. exact (TRANS (@lem5443223) (@lem5443234)). Qed.
Lemma lem5443236 : term764 = False.
Proof. exact (TRANS (@lem5443220) (@lem5443235)). Qed.
Lemma lem5443237 : term761 = False.
Proof. exact (TRANS (@lem5443204) (@lem5443236)). Qed.
Lemma lem5443238 : term759 = False.
Proof. exact (TRANS (@lem5443181) (@lem5443237)). Qed.
Lemma lem5443239 : term758 = False.
Proof. exact (TRANS (@lem5443172) (@lem5443238)). Qed.
Lemma lem5443240 (_70504 : int) (_70506 : int) (_70507 : int) (_70505 : int) (_70508 : int) (h1 : term679 _70504 _70506 _70507 _70505 _70508) : False.
Proof. exact (EQ_MP (@lem5443239) (@lem5443169 _70504 _70506 _70507 _70505 _70508 h1)). Qed.
Lemma lem5443241 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term691 _70504 _70505 _70506 _70507 _70508) : term691 _70504 _70505 _70506 _70507 _70508.
Proof. exact (h1). Qed.
Lemma lem5443242 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term691 _70504 _70505 _70506 _70507 _70508) : term690 _70504 _70505 _70506 _70507 _70508.
Proof. exact (proj2 (@lem5443241 _70504 _70505 _70506 _70507 _70508 h1)). Qed.
Lemma lem5443244 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term691 _70504 _70505 _70506 _70507 _70508) : term689 _70504 _70505 _70506 _70507 _70508.
Proof. exact (proj2 (@lem5443242 _70504 _70505 _70506 _70507 _70508 h1)). Qed.
Lemma lem5443246 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term691 _70504 _70505 _70506 _70507 _70508) : term687 _70504 _70505 _70506 _70507 _70508.
Proof. exact (proj2 (@lem5443244 _70504 _70505 _70506 _70507 _70508 h1)). Qed.
Lemma lem5443248 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term691 _70504 _70505 _70506 _70507 _70508) : term685 _70504 _70505 _70506 _70507 _70508.
Proof. exact (proj2 (@lem5443246 _70504 _70505 _70506 _70507 _70508 h1)). Qed.
Lemma lem5443250 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term691 _70504 _70505 _70506 _70507 _70508) : term683 _70504 _70505 _70506 _70507 _70508.
Proof. exact (proj2 (@lem5443248 _70504 _70505 _70506 _70507 _70508 h1)). Qed.
Lemma lem5443252 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term691 _70504 _70505 _70506 _70507 _70508) : term681 _70504 _70505 _70506 _70507 _70508.
Proof. exact (proj2 (@lem5443250 _70504 _70505 _70506 _70507 _70508 h1)). Qed.
Lemma lem5443254 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term691 _70504 _70505 _70506 _70507 _70508) : term338 _70507 _70508.
Proof. exact (proj2 (@lem5443252 _70504 _70505 _70506 _70507 _70508 h1)). Qed.
Lemma lem5443255 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term691 _70504 _70505 _70506 _70507 _70508) : term372 _70504 _70505 _70506 _70507 _70508.
Proof. exact (proj1 (@lem5443252 _70504 _70505 _70506 _70507 _70508 h1)). Qed.
Lemma lem5443256 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term691 _70504 _70505 _70506 _70507 _70508) : term370 _70506 _70507 _70508.
Proof. exact (proj2 (@lem5443255 _70504 _70505 _70506 _70507 _70508 h1)). Qed.
Lemma lem5443260 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term691 _70504 _70505 _70506 _70507 _70508) : term368 _70507 _70508.
Proof. exact (proj2 (@lem5443256 _70504 _70505 _70506 _70507 _70508 h1)). Qed.
Lemma lem5443263 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5443264 : term699 = term700.
Proof. exact (@lem5443263 term214 term227). Qed.
Lemma lem5443266 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5443267 : term227 = term320.
Proof. exact (@lem5443266 term228). Qed.
Lemma lem5443269 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5443270 : term214 = term291.
Proof. exact (@lem5443269 (NUMERAL 0)). Qed.
Lemma lem5443271 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5443272 : term701 = term702.
Proof. exact (MK_COMB (@lem5443271) (@lem5443270)). Qed.
Lemma lem5443273 : term700 = term703.
Proof. exact (MK_COMB (@lem5443272) (@lem5443267)). Qed.
Lemma lem5443274 : term704.
Proof. exact (@lem1980255 term214 term227 term227 term227). Qed.
Lemma lem5443276 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5443277 : term700 = term706.
Proof. exact (@lem5443276 (NUMERAL 0) term228). Qed.
Lemma lem5443278 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5443279 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5443280 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5443279 h1) (fun h1 : term706 = True => @lem5443278)). Qed.
Lemma lem5443281 : term706 = True.
Proof. exact (EQ_MP (@lem5443280) (@lem5443278)). Qed.
Lemma lem5443282 : term700 = True.
Proof. exact (TRANS (@lem5443277) (@lem5443281)). Qed.
Lemma lem5443283 : True = term700.
Proof. exact (SYM (@lem5443282)). Qed.
Lemma lem5443284 : term700.
Proof. exact (EQ_MP (@lem5443283) (@lem0)). Qed.
Lemma lem5443285 : term708.
Proof. exact (@lem5443274 (@lem5443284)). Qed.
Lemma lem5443287 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5443288 : term700 = term706.
Proof. exact (@lem5443287 (NUMERAL 0) term228). Qed.
Lemma lem5443289 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5443290 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5443291 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5443290 h1) (fun h1 : term706 = True => @lem5443289)). Qed.
Lemma lem5443292 : term706 = True.
Proof. exact (EQ_MP (@lem5443291) (@lem5443289)). Qed.
Lemma lem5443293 : term700 = True.
Proof. exact (TRANS (@lem5443288) (@lem5443292)). Qed.
Lemma lem5443294 : True = term700.
Proof. exact (SYM (@lem5443293)). Qed.
Lemma lem5443295 : term700.
Proof. exact (EQ_MP (@lem5443294) (@lem0)). Qed.
Lemma lem5443296 : term703 = term709.
Proof. exact (@lem5443285 (@lem5443295)). Qed.
Lemma lem5443298 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5443299 : term303 = term304.
Proof. exact (@lem5443298 term228 term228). Qed.
Lemma lem5443300 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5443301 : term306 = term228.
Proof. exact (EQ_MP (@lem5443300) (@lem940073)). Qed.
Lemma lem5443302 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5443303 : term304 = term227.
Proof. exact (MK_COMB (@lem5443302) (@lem5443301)). Qed.
Lemma lem5443304 : term303 = term227.
Proof. exact (TRANS (@lem5443299) (@lem5443303)). Qed.
Lemma lem5443306 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5443307 : term711 = term214.
Proof. exact (@lem5443306 term228). Qed.
Lemma lem5443308 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5443309 : term712 = term701.
Proof. exact (MK_COMB (@lem5443308) (@lem5443307)). Qed.
Lemma lem5443310 : term709 = term700.
Proof. exact (MK_COMB (@lem5443309) (@lem5443304)). Qed.
Lemma lem5443312 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5443313 : term700 = term706.
Proof. exact (@lem5443312 (NUMERAL 0) term228). Qed.
Lemma lem5443314 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5443315 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5443316 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5443315 h1) (fun h1 : term706 = True => @lem5443314)). Qed.
Lemma lem5443317 : term706 = True.
Proof. exact (EQ_MP (@lem5443316) (@lem5443314)). Qed.
Lemma lem5443318 : term700 = True.
Proof. exact (TRANS (@lem5443313) (@lem5443317)). Qed.
Lemma lem5443319 : term709 = True.
Proof. exact (TRANS (@lem5443310) (@lem5443318)). Qed.
Lemma lem5443320 : term703 = True.
Proof. exact (TRANS (@lem5443296) (@lem5443319)). Qed.
Lemma lem5443321 : term700 = True.
Proof. exact (TRANS (@lem5443273) (@lem5443320)). Qed.
Lemma lem5443322 : term699 = True.
Proof. exact (TRANS (@lem5443264) (@lem5443321)). Qed.
Lemma lem5443323 : True = term699.
Proof. exact (SYM (@lem5443322)). Qed.
Lemma lem5443324 : term699.
Proof. exact (EQ_MP (@lem5443323) (@lem0)). Qed.
Lemma lem5443325 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term691 _70504 _70505 _70506 _70507 _70508) : term770 _70507 _70508.
Proof. exact (conj (@lem5443324) (@lem5443260 _70504 _70505 _70506 _70507 _70508 h1)). Qed.
Lemma lem5443327 (x : real) (y : real) : term714 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5443328 (_70507 : int) (_70508 : int) : term771 _70507 _70508.
Proof. exact (@lem5443327 term227 (term362 _70507 _70508)). Qed.
Lemma lem5443329 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term691 _70504 _70505 _70506 _70507 _70508) : term772 _70507 _70508.
Proof. exact (@lem5443328 _70507 _70508 (@lem5443325 _70504 _70505 _70506 _70507 _70508 h1)). Qed.
Lemma lem5443330 (_70507 : int) (_70508 : int) : (term773 _70507 _70508) = (term362 _70507 _70508).
Proof. exact (@lem1982733 (term362 _70507 _70508)). Qed.
Lemma lem5443331 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5443332 (_70507 : int) (_70508 : int) : (term774 _70507 _70508) = (term367 _70507 _70508).
Proof. exact (MK_COMB (@lem5443331) (@lem5443330 _70507 _70508)). Qed.
Lemma lem5443333 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5443334 (_70507 : int) (_70508 : int) : (term772 _70507 _70508) = (term368 _70507 _70508).
Proof. exact (MK_COMB (@lem5443332 _70507 _70508) (@lem5443333)). Qed.
Lemma lem5443335 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term691 _70504 _70505 _70506 _70507 _70508) : term368 _70507 _70508.
Proof. exact (EQ_MP (@lem5443334 _70507 _70508) (@lem5443329 _70504 _70505 _70506 _70507 _70508 h1)). Qed.
Lemma lem5443337 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5443338 : term699 = term700.
Proof. exact (@lem5443337 term214 term227). Qed.
Lemma lem5443340 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5443341 : term227 = term320.
Proof. exact (@lem5443340 term228). Qed.
Lemma lem5443343 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5443344 : term214 = term291.
Proof. exact (@lem5443343 (NUMERAL 0)). Qed.
Lemma lem5443345 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5443346 : term701 = term702.
Proof. exact (MK_COMB (@lem5443345) (@lem5443344)). Qed.
Lemma lem5443347 : term700 = term703.
Proof. exact (MK_COMB (@lem5443346) (@lem5443341)). Qed.
Lemma lem5443348 : term704.
Proof. exact (@lem1980255 term214 term227 term227 term227). Qed.
Lemma lem5443350 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5443351 : term700 = term706.
Proof. exact (@lem5443350 (NUMERAL 0) term228). Qed.
Lemma lem5443352 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5443353 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5443354 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5443353 h1) (fun h1 : term706 = True => @lem5443352)). Qed.
Lemma lem5443355 : term706 = True.
Proof. exact (EQ_MP (@lem5443354) (@lem5443352)). Qed.
Lemma lem5443356 : term700 = True.
Proof. exact (TRANS (@lem5443351) (@lem5443355)). Qed.
Lemma lem5443357 : True = term700.
Proof. exact (SYM (@lem5443356)). Qed.
Lemma lem5443358 : term700.
Proof. exact (EQ_MP (@lem5443357) (@lem0)). Qed.
Lemma lem5443359 : term708.
Proof. exact (@lem5443348 (@lem5443358)). Qed.
Lemma lem5443361 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5443362 : term700 = term706.
Proof. exact (@lem5443361 (NUMERAL 0) term228). Qed.
Lemma lem5443363 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5443364 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5443365 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5443364 h1) (fun h1 : term706 = True => @lem5443363)). Qed.
Lemma lem5443366 : term706 = True.
Proof. exact (EQ_MP (@lem5443365) (@lem5443363)). Qed.
Lemma lem5443367 : term700 = True.
Proof. exact (TRANS (@lem5443362) (@lem5443366)). Qed.
Lemma lem5443368 : True = term700.
Proof. exact (SYM (@lem5443367)). Qed.
Lemma lem5443369 : term700.
Proof. exact (EQ_MP (@lem5443368) (@lem0)). Qed.
Lemma lem5443370 : term703 = term709.
Proof. exact (@lem5443359 (@lem5443369)). Qed.
Lemma lem5443372 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5443373 : term303 = term304.
Proof. exact (@lem5443372 term228 term228). Qed.
Lemma lem5443374 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5443375 : term306 = term228.
Proof. exact (EQ_MP (@lem5443374) (@lem940073)). Qed.
Lemma lem5443376 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5443377 : term304 = term227.
Proof. exact (MK_COMB (@lem5443376) (@lem5443375)). Qed.
Lemma lem5443378 : term303 = term227.
Proof. exact (TRANS (@lem5443373) (@lem5443377)). Qed.
Lemma lem5443380 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5443381 : term711 = term214.
Proof. exact (@lem5443380 term228). Qed.
Lemma lem5443382 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5443383 : term712 = term701.
Proof. exact (MK_COMB (@lem5443382) (@lem5443381)). Qed.
Lemma lem5443384 : term709 = term700.
Proof. exact (MK_COMB (@lem5443383) (@lem5443378)). Qed.
Lemma lem5443386 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5443387 : term700 = term706.
Proof. exact (@lem5443386 (NUMERAL 0) term228). Qed.
Lemma lem5443388 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5443389 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5443390 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5443389 h1) (fun h1 : term706 = True => @lem5443388)). Qed.
Lemma lem5443391 : term706 = True.
Proof. exact (EQ_MP (@lem5443390) (@lem5443388)). Qed.
Lemma lem5443392 : term700 = True.
Proof. exact (TRANS (@lem5443387) (@lem5443391)). Qed.
Lemma lem5443393 : term709 = True.
Proof. exact (TRANS (@lem5443384) (@lem5443392)). Qed.
Lemma lem5443394 : term703 = True.
Proof. exact (TRANS (@lem5443370) (@lem5443393)). Qed.
Lemma lem5443395 : term700 = True.
Proof. exact (TRANS (@lem5443347) (@lem5443394)). Qed.
Lemma lem5443396 : term699 = True.
Proof. exact (TRANS (@lem5443338) (@lem5443395)). Qed.
Lemma lem5443397 : True = term699.
Proof. exact (SYM (@lem5443396)). Qed.
Lemma lem5443398 : term699.
Proof. exact (EQ_MP (@lem5443397) (@lem0)). Qed.
Lemma lem5443399 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term691 _70504 _70505 _70506 _70507 _70508) : term775 _70507 _70508.
Proof. exact (conj (@lem5443398) (@lem5443254 _70504 _70505 _70506 _70507 _70508 h1)). Qed.
Lemma lem5443401 (x : real) (y : real) : term714 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5443402 (_70507 : int) (_70508 : int) : term776 _70507 _70508.
Proof. exact (@lem5443401 term227 (term335 _70507 _70508)). Qed.
Lemma lem5443403 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term691 _70504 _70505 _70506 _70507 _70508) : term777 _70507 _70508.
Proof. exact (@lem5443402 _70507 _70508 (@lem5443399 _70504 _70505 _70506 _70507 _70508 h1)). Qed.
Lemma lem5443404 (_70507 : int) (_70508 : int) : (term778 _70507 _70508) = (term335 _70507 _70508).
Proof. exact (@lem1982733 (term335 _70507 _70508)). Qed.
Lemma lem5443405 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5443406 (_70507 : int) (_70508 : int) : (term779 _70507 _70508) = (term337 _70507 _70508).
Proof. exact (MK_COMB (@lem5443405) (@lem5443404 _70507 _70508)). Qed.
Lemma lem5443407 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5443408 (_70507 : int) (_70508 : int) : (term777 _70507 _70508) = (term338 _70507 _70508).
Proof. exact (MK_COMB (@lem5443406 _70507 _70508) (@lem5443407)). Qed.
Lemma lem5443409 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term691 _70504 _70505 _70506 _70507 _70508) : term338 _70507 _70508.
Proof. exact (EQ_MP (@lem5443408 _70507 _70508) (@lem5443403 _70504 _70505 _70506 _70507 _70508 h1)). Qed.
Lemma lem5443410 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term691 _70504 _70505 _70506 _70507 _70508) : term780 _70507 _70508.
Proof. exact (conj (@lem5443409 _70504 _70505 _70506 _70507 _70508 h1) (@lem5443335 _70504 _70505 _70506 _70507 _70508 h1)). Qed.
Lemma lem5443412 (x : real) (y : real) : term725 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5443413 (_70507 : int) (_70508 : int) : term781 _70507 _70508.
Proof. exact (@lem5443412 (term335 _70507 _70508) (term362 _70507 _70508)). Qed.
Lemma lem5443414 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term691 _70504 _70505 _70506 _70507 _70508) : term782 _70507 _70508.
Proof. exact (@lem5443413 _70507 _70508 (@lem5443410 _70504 _70505 _70506 _70507 _70508 h1)). Qed.
Lemma lem5443415 (_70507 : int) (_70508 : int) : (term783 _70507 _70508) = (term784 _70507 _70508).
Proof. exact (@lem1982753 (term336 _70507) (real_of_int _70507) (term785 _70508) (term336 _70508)). Qed.
Lemma lem5443416 (_70507 : int) : (term730 _70507) = (term731 _70507).
Proof. exact (@lem1982713 term294 (real_of_int _70507)). Qed.
Lemma lem5443418 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5443419 : term227 = term320.
Proof. exact (@lem5443418 term228). Qed.
Lemma lem5443421 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5443422 : term294 = term295.
Proof. exact (@lem5443421 term228). Qed.
Lemma lem5443423 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5443424 : term732 = term733.
Proof. exact (MK_COMB (@lem5443423) (@lem5443422)). Qed.
Lemma lem5443425 : term734 = term735.
Proof. exact (MK_COMB (@lem5443424) (@lem5443419)). Qed.
Lemma lem5443426 : term736.
Proof. exact (@lem1981473 term294 term227 term227 term227 term214 term227). Qed.
Lemma lem5443428 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5443429 : term700 = term706.
Proof. exact (@lem5443428 (NUMERAL 0) term228). Qed.
Lemma lem5443430 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5443431 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5443432 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5443431 h1) (fun h1 : term706 = True => @lem5443430)). Qed.
Lemma lem5443433 : term706 = True.
Proof. exact (EQ_MP (@lem5443432) (@lem5443430)). Qed.
Lemma lem5443434 : term700 = True.
Proof. exact (TRANS (@lem5443429) (@lem5443433)). Qed.
Lemma lem5443435 : True = term700.
Proof. exact (SYM (@lem5443434)). Qed.
Lemma lem5443436 : term700.
Proof. exact (EQ_MP (@lem5443435) (@lem0)). Qed.
Lemma lem5443437 : term737.
Proof. exact (@lem5443426 (@lem5443436)). Qed.
Lemma lem5443439 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5443440 : term700 = term706.
Proof. exact (@lem5443439 (NUMERAL 0) term228). Qed.
Lemma lem5443441 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5443442 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5443443 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5443442 h1) (fun h1 : term706 = True => @lem5443441)). Qed.
Lemma lem5443444 : term706 = True.
Proof. exact (EQ_MP (@lem5443443) (@lem5443441)). Qed.
Lemma lem5443445 : term700 = True.
Proof. exact (TRANS (@lem5443440) (@lem5443444)). Qed.
Lemma lem5443446 : True = term700.
Proof. exact (SYM (@lem5443445)). Qed.
Lemma lem5443447 : term700.
Proof. exact (EQ_MP (@lem5443446) (@lem0)). Qed.
Lemma lem5443448 : term738.
Proof. exact (@lem5443437 (@lem5443447)). Qed.
Lemma lem5443450 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5443451 : term700 = term706.
Proof. exact (@lem5443450 (NUMERAL 0) term228). Qed.
Lemma lem5443452 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5443453 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5443454 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5443453 h1) (fun h1 : term706 = True => @lem5443452)). Qed.
Lemma lem5443455 : term706 = True.
Proof. exact (EQ_MP (@lem5443454) (@lem5443452)). Qed.
Lemma lem5443456 : term700 = True.
Proof. exact (TRANS (@lem5443451) (@lem5443455)). Qed.
Lemma lem5443457 : True = term700.
Proof. exact (SYM (@lem5443456)). Qed.
Lemma lem5443458 : term700.
Proof. exact (EQ_MP (@lem5443457) (@lem0)). Qed.
Lemma lem5443459 : term739.
Proof. exact (@lem5443448 (@lem5443458)). Qed.
Lemma lem5443461 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5443462 : term303 = term304.
Proof. exact (@lem5443461 term228 term228). Qed.
Lemma lem5443463 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5443464 : term306 = term228.
Proof. exact (EQ_MP (@lem5443463) (@lem940073)). Qed.
Lemma lem5443465 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5443466 : term304 = term227.
Proof. exact (MK_COMB (@lem5443465) (@lem5443464)). Qed.
Lemma lem5443467 : term303 = term227.
Proof. exact (TRANS (@lem5443462) (@lem5443466)). Qed.
Lemma lem5443469 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5443470 : term321 = term326.
Proof. exact (@lem5443469 term228 term228). Qed.
Lemma lem5443471 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5443472 : term306 = term228.
Proof. exact (EQ_MP (@lem5443471) (@lem940073)). Qed.
Lemma lem5443473 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5443474 : term304 = term227.
Proof. exact (MK_COMB (@lem5443473) (@lem5443472)). Qed.
Lemma lem5443475 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5443476 : term326 = term294.
Proof. exact (MK_COMB (@lem5443475) (@lem5443474)). Qed.
Lemma lem5443477 : term321 = term294.
Proof. exact (TRANS (@lem5443470) (@lem5443476)). Qed.
Lemma lem5443478 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5443479 : term740 = term732.
Proof. exact (MK_COMB (@lem5443478) (@lem5443477)). Qed.
Lemma lem5443480 : term741 = term734.
Proof. exact (MK_COMB (@lem5443479) (@lem5443467)). Qed.
Lemma lem5443482 (m : nat) : (term742 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5443483 : term734 = term214.
Proof. exact (@lem5443482 term228). Qed.
Lemma lem5443484 : term741 = term214.
Proof. exact (TRANS (@lem5443480) (@lem5443483)). Qed.
Lemma lem5443485 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5443486 : term743 = term744.
Proof. exact (MK_COMB (@lem5443485) (@lem5443484)). Qed.
Lemma lem5443487 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem5443488 : term745 = term711.
Proof. exact (MK_COMB (@lem5443486) (@lem5443487)). Qed.
Lemma lem5443490 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5443491 : term711 = term214.
Proof. exact (@lem5443490 term228). Qed.
Lemma lem5443492 : term745 = term214.
Proof. exact (TRANS (@lem5443488) (@lem5443491)). Qed.
Lemma lem5443494 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5443495 : term303 = term304.
Proof. exact (@lem5443494 term228 term228). Qed.
Lemma lem5443496 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5443497 : term306 = term228.
Proof. exact (EQ_MP (@lem5443496) (@lem940073)). Qed.
Lemma lem5443498 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5443499 : term304 = term227.
Proof. exact (MK_COMB (@lem5443498) (@lem5443497)). Qed.
Lemma lem5443500 : term303 = term227.
Proof. exact (TRANS (@lem5443495) (@lem5443499)). Qed.
Lemma lem5443501 : term744 = term744.
Proof. exact (eq_refl term744). Qed.
Lemma lem5443502 : term746 = term711.
Proof. exact (MK_COMB (@lem5443501) (@lem5443500)). Qed.
Lemma lem5443504 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5443505 : term711 = term214.
Proof. exact (@lem5443504 term228). Qed.
Lemma lem5443506 : term746 = term214.
Proof. exact (TRANS (@lem5443502) (@lem5443505)). Qed.
Lemma lem5443507 : term214 = term746.
Proof. exact (SYM (@lem5443506)). Qed.
Lemma lem5443508 : term745 = term746.
Proof. exact (TRANS (@lem5443492) (@lem5443507)). Qed.
Lemma lem5443509 : term735 = term291.
Proof. exact (@lem5443459 (@lem5443508)). Qed.
Lemma lem5443510 : term734 = term291.
Proof. exact (TRANS (@lem5443425) (@lem5443509)). Qed.
Lemma lem5443512 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5443513 : term291 = term214.
Proof. exact (@lem5443512 term214). Qed.
Lemma lem5443514 : term734 = term214.
Proof. exact (TRANS (@lem5443510) (@lem5443513)). Qed.
Lemma lem5443515 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5443516 : term747 = term744.
Proof. exact (MK_COMB (@lem5443515) (@lem5443514)). Qed.
Lemma lem5443517 (_70507 : int) : (real_of_int _70507) = (real_of_int _70507).
Proof. exact (eq_refl (real_of_int _70507)). Qed.
Lemma lem5443518 (_70507 : int) : (term731 _70507) = (term748 _70507).
Proof. exact (MK_COMB (@lem5443516) (@lem5443517 _70507)). Qed.
Lemma lem5443519 (_70507 : int) : (term730 _70507) = (term748 _70507).
Proof. exact (TRANS (@lem5443416 _70507) (@lem5443518 _70507)). Qed.
Lemma lem5443520 (_70507 : int) : (term748 _70507) = term214.
Proof. exact (@lem1982719 (real_of_int _70507)). Qed.
Lemma lem5443521 (_70507 : int) : (term730 _70507) = term214.
Proof. exact (TRANS (@lem5443519 _70507) (@lem5443520 _70507)). Qed.
Lemma lem5443522 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5443523 (_70507 : int) : (term749 _70507) = term750.
Proof. exact (MK_COMB (@lem5443522) (@lem5443521 _70507)). Qed.
Lemma lem5443524 (_70508 : int) : (term786 _70508) = (term752 _70508).
Proof. exact (@lem1982759 (real_of_int _70508) (term336 _70508) term294). Qed.
Lemma lem5443525 (_70508 : int) : (term753 _70508) = (term731 _70508).
Proof. exact (@lem1982715 term294 (real_of_int _70508)). Qed.
Lemma lem5443527 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5443528 : term227 = term320.
Proof. exact (@lem5443527 term228). Qed.
Lemma lem5443530 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5443531 : term294 = term295.
Proof. exact (@lem5443530 term228). Qed.
Lemma lem5443532 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5443533 : term732 = term733.
Proof. exact (MK_COMB (@lem5443532) (@lem5443531)). Qed.
Lemma lem5443534 : term734 = term735.
Proof. exact (MK_COMB (@lem5443533) (@lem5443528)). Qed.
Lemma lem5443535 : term736.
Proof. exact (@lem1981473 term294 term227 term227 term227 term214 term227). Qed.
Lemma lem5443537 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5443538 : term700 = term706.
Proof. exact (@lem5443537 (NUMERAL 0) term228). Qed.
Lemma lem5443539 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5443540 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5443541 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5443540 h1) (fun h1 : term706 = True => @lem5443539)). Qed.
Lemma lem5443542 : term706 = True.
Proof. exact (EQ_MP (@lem5443541) (@lem5443539)). Qed.
Lemma lem5443543 : term700 = True.
Proof. exact (TRANS (@lem5443538) (@lem5443542)). Qed.
Lemma lem5443544 : True = term700.
Proof. exact (SYM (@lem5443543)). Qed.
Lemma lem5443545 : term700.
Proof. exact (EQ_MP (@lem5443544) (@lem0)). Qed.
Lemma lem5443546 : term737.
Proof. exact (@lem5443535 (@lem5443545)). Qed.
Lemma lem5443548 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5443549 : term700 = term706.
Proof. exact (@lem5443548 (NUMERAL 0) term228). Qed.
Lemma lem5443550 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5443551 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5443552 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5443551 h1) (fun h1 : term706 = True => @lem5443550)). Qed.
Lemma lem5443553 : term706 = True.
Proof. exact (EQ_MP (@lem5443552) (@lem5443550)). Qed.
Lemma lem5443554 : term700 = True.
Proof. exact (TRANS (@lem5443549) (@lem5443553)). Qed.
Lemma lem5443555 : True = term700.
Proof. exact (SYM (@lem5443554)). Qed.
Lemma lem5443556 : term700.
Proof. exact (EQ_MP (@lem5443555) (@lem0)). Qed.
Lemma lem5443557 : term738.
Proof. exact (@lem5443546 (@lem5443556)). Qed.
Lemma lem5443559 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5443560 : term700 = term706.
Proof. exact (@lem5443559 (NUMERAL 0) term228). Qed.
Lemma lem5443561 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5443562 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5443563 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5443562 h1) (fun h1 : term706 = True => @lem5443561)). Qed.
Lemma lem5443564 : term706 = True.
Proof. exact (EQ_MP (@lem5443563) (@lem5443561)). Qed.
Lemma lem5443565 : term700 = True.
Proof. exact (TRANS (@lem5443560) (@lem5443564)). Qed.
Lemma lem5443566 : True = term700.
Proof. exact (SYM (@lem5443565)). Qed.
Lemma lem5443567 : term700.
Proof. exact (EQ_MP (@lem5443566) (@lem0)). Qed.
Lemma lem5443568 : term739.
Proof. exact (@lem5443557 (@lem5443567)). Qed.
Lemma lem5443570 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5443571 : term303 = term304.
Proof. exact (@lem5443570 term228 term228). Qed.
Lemma lem5443572 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5443573 : term306 = term228.
Proof. exact (EQ_MP (@lem5443572) (@lem940073)). Qed.
Lemma lem5443574 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5443575 : term304 = term227.
Proof. exact (MK_COMB (@lem5443574) (@lem5443573)). Qed.
Lemma lem5443576 : term303 = term227.
Proof. exact (TRANS (@lem5443571) (@lem5443575)). Qed.
Lemma lem5443578 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5443579 : term321 = term326.
Proof. exact (@lem5443578 term228 term228). Qed.
Lemma lem5443580 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5443581 : term306 = term228.
Proof. exact (EQ_MP (@lem5443580) (@lem940073)). Qed.
Lemma lem5443582 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5443583 : term304 = term227.
Proof. exact (MK_COMB (@lem5443582) (@lem5443581)). Qed.
Lemma lem5443584 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5443585 : term326 = term294.
Proof. exact (MK_COMB (@lem5443584) (@lem5443583)). Qed.
Lemma lem5443586 : term321 = term294.
Proof. exact (TRANS (@lem5443579) (@lem5443585)). Qed.
Lemma lem5443587 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5443588 : term740 = term732.
Proof. exact (MK_COMB (@lem5443587) (@lem5443586)). Qed.
Lemma lem5443589 : term741 = term734.
Proof. exact (MK_COMB (@lem5443588) (@lem5443576)). Qed.
Lemma lem5443591 (m : nat) : (term742 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5443592 : term734 = term214.
Proof. exact (@lem5443591 term228). Qed.
Lemma lem5443593 : term741 = term214.
Proof. exact (TRANS (@lem5443589) (@lem5443592)). Qed.
Lemma lem5443594 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5443595 : term743 = term744.
Proof. exact (MK_COMB (@lem5443594) (@lem5443593)). Qed.
Lemma lem5443596 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem5443597 : term745 = term711.
Proof. exact (MK_COMB (@lem5443595) (@lem5443596)). Qed.
Lemma lem5443599 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5443600 : term711 = term214.
Proof. exact (@lem5443599 term228). Qed.
Lemma lem5443601 : term745 = term214.
Proof. exact (TRANS (@lem5443597) (@lem5443600)). Qed.
Lemma lem5443603 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5443604 : term303 = term304.
Proof. exact (@lem5443603 term228 term228). Qed.
Lemma lem5443605 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5443606 : term306 = term228.
Proof. exact (EQ_MP (@lem5443605) (@lem940073)). Qed.
Lemma lem5443607 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5443608 : term304 = term227.
Proof. exact (MK_COMB (@lem5443607) (@lem5443606)). Qed.
Lemma lem5443609 : term303 = term227.
Proof. exact (TRANS (@lem5443604) (@lem5443608)). Qed.
Lemma lem5443610 : term744 = term744.
Proof. exact (eq_refl term744). Qed.
Lemma lem5443611 : term746 = term711.
Proof. exact (MK_COMB (@lem5443610) (@lem5443609)). Qed.
Lemma lem5443613 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5443614 : term711 = term214.
Proof. exact (@lem5443613 term228). Qed.
Lemma lem5443615 : term746 = term214.
Proof. exact (TRANS (@lem5443611) (@lem5443614)). Qed.
Lemma lem5443616 : term214 = term746.
Proof. exact (SYM (@lem5443615)). Qed.
Lemma lem5443617 : term745 = term746.
Proof. exact (TRANS (@lem5443601) (@lem5443616)). Qed.
Lemma lem5443618 : term735 = term291.
Proof. exact (@lem5443568 (@lem5443617)). Qed.
Lemma lem5443619 : term734 = term291.
Proof. exact (TRANS (@lem5443534) (@lem5443618)). Qed.
Lemma lem5443621 (x : real) : (term310 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5443622 : term291 = term214.
Proof. exact (@lem5443621 term214). Qed.
Lemma lem5443623 : term734 = term214.
Proof. exact (TRANS (@lem5443619) (@lem5443622)). Qed.
Lemma lem5443624 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5443625 : term747 = term744.
Proof. exact (MK_COMB (@lem5443624) (@lem5443623)). Qed.
Lemma lem5443626 (_70508 : int) : (real_of_int _70508) = (real_of_int _70508).
Proof. exact (eq_refl (real_of_int _70508)). Qed.
Lemma lem5443627 (_70508 : int) : (term731 _70508) = (term748 _70508).
Proof. exact (MK_COMB (@lem5443625) (@lem5443626 _70508)). Qed.
Lemma lem5443628 (_70508 : int) : (term753 _70508) = (term748 _70508).
Proof. exact (TRANS (@lem5443525 _70508) (@lem5443627 _70508)). Qed.
Lemma lem5443629 (_70508 : int) : (term748 _70508) = term214.
Proof. exact (@lem1982719 (real_of_int _70508)). Qed.
Lemma lem5443630 (_70508 : int) : (term753 _70508) = term214.
Proof. exact (TRANS (@lem5443628 _70508) (@lem5443629 _70508)). Qed.
Lemma lem5443631 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5443632 (_70508 : int) : (term754 _70508) = term750.
Proof. exact (MK_COMB (@lem5443631) (@lem5443630 _70508)). Qed.
Lemma lem5443633 : term294 = term294.
Proof. exact (eq_refl term294). Qed.
Lemma lem5443634 (_70508 : int) : (term752 _70508) = term755.
Proof. exact (MK_COMB (@lem5443632 _70508) (@lem5443633)). Qed.
Lemma lem5443635 (_70508 : int) : (term786 _70508) = term755.
Proof. exact (TRANS (@lem5443524 _70508) (@lem5443634 _70508)). Qed.
Lemma lem5443636 : term755 = term294.
Proof. exact (@lem1982721 term294). Qed.
Lemma lem5443637 (_70508 : int) : (term786 _70508) = term294.
Proof. exact (TRANS (@lem5443635 _70508) (@lem5443636)). Qed.
Lemma lem5443638 (_70507 : int) (_70508 : int) : (term784 _70507 _70508) = term755.
Proof. exact (MK_COMB (@lem5443523 _70507) (@lem5443637 _70508)). Qed.
Lemma lem5443639 (_70507 : int) (_70508 : int) : (term783 _70507 _70508) = term755.
Proof. exact (TRANS (@lem5443415 _70507 _70508) (@lem5443638 _70507 _70508)). Qed.
Lemma lem5443640 : term755 = term294.
Proof. exact (@lem1982721 term294). Qed.
Lemma lem5443641 (_70507 : int) (_70508 : int) : (term783 _70507 _70508) = term294.
Proof. exact (TRANS (@lem5443639 _70507 _70508) (@lem5443640)). Qed.
Lemma lem5443642 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5443643 (_70507 : int) (_70508 : int) : (term787 _70507 _70508) = term757.
Proof. exact (MK_COMB (@lem5443642) (@lem5443641 _70507 _70508)). Qed.
Lemma lem5443644 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5443645 (_70507 : int) (_70508 : int) : (term782 _70507 _70508) = term758.
Proof. exact (MK_COMB (@lem5443643 _70507 _70508) (@lem5443644)). Qed.
Lemma lem5443646 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term691 _70504 _70505 _70506 _70507 _70508) : term758.
Proof. exact (EQ_MP (@lem5443645 _70507 _70508) (@lem5443414 _70504 _70505 _70506 _70507 _70508 h1)). Qed.
Lemma lem5443648 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5443649 : term758 = term759.
Proof. exact (@lem5443648 term214 term294). Qed.
Lemma lem5443651 (x : nat) : (term292 x) = (term293 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5443652 : term294 = term295.
Proof. exact (@lem5443651 term228). Qed.
Lemma lem5443654 (x : nat) : (real_of_num x) = (term290 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5443655 : term214 = term291.
Proof. exact (@lem5443654 (NUMERAL 0)). Qed.
Lemma lem5443656 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5443657 : term216 = term760.
Proof. exact (MK_COMB (@lem5443656) (@lem5443655)). Qed.
Lemma lem5443658 : term759 = term761.
Proof. exact (MK_COMB (@lem5443657) (@lem5443652)). Qed.
Lemma lem5443659 : term762.
Proof. exact (@lem1980026 term214 term227 term294 term227). Qed.
Lemma lem5443661 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5443662 : term700 = term706.
Proof. exact (@lem5443661 (NUMERAL 0) term228). Qed.
Lemma lem5443663 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5443664 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5443665 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5443664 h1) (fun h1 : term706 = True => @lem5443663)). Qed.
Lemma lem5443666 : term706 = True.
Proof. exact (EQ_MP (@lem5443665) (@lem5443663)). Qed.
Lemma lem5443667 : term700 = True.
Proof. exact (TRANS (@lem5443662) (@lem5443666)). Qed.
Lemma lem5443668 : True = term700.
Proof. exact (SYM (@lem5443667)). Qed.
Lemma lem5443669 : term700.
Proof. exact (EQ_MP (@lem5443668) (@lem0)). Qed.
Lemma lem5443670 : term763.
Proof. exact (@lem5443659 (@lem5443669)). Qed.
Lemma lem5443672 (m : nat) (n : nat) : (term705 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5443673 : term700 = term706.
Proof. exact (@lem5443672 (NUMERAL 0) term228). Qed.
Lemma lem5443674 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5443675 (h1 : term707 = (BIT1 0)) : term706 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5443676 : (term707 = (BIT1 0)) = (term706 = True).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5443675 h1) (fun h1 : term706 = True => @lem5443674)). Qed.
Lemma lem5443677 : term706 = True.
Proof. exact (EQ_MP (@lem5443676) (@lem5443674)). Qed.
Lemma lem5443678 : term700 = True.
Proof. exact (TRANS (@lem5443673) (@lem5443677)). Qed.
Lemma lem5443679 : True = term700.
Proof. exact (SYM (@lem5443678)). Qed.
Lemma lem5443680 : term700.
Proof. exact (EQ_MP (@lem5443679) (@lem0)). Qed.
Lemma lem5443681 : term761 = term764.
Proof. exact (@lem5443670 (@lem5443680)). Qed.
Lemma lem5443683 (m : nat) (n : nat) : (term324 m n) = (term325 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5443684 : term321 = term326.
Proof. exact (@lem5443683 term228 term228). Qed.
Lemma lem5443685 : (term305 = (BIT1 0)) = (term306 = term228).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5443686 : term306 = term228.
Proof. exact (EQ_MP (@lem5443685) (@lem940073)). Qed.
Lemma lem5443687 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5443688 : term304 = term227.
Proof. exact (MK_COMB (@lem5443687) (@lem5443686)). Qed.
Lemma lem5443689 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5443690 : term326 = term294.
Proof. exact (MK_COMB (@lem5443689) (@lem5443688)). Qed.
Lemma lem5443691 : term321 = term294.
Proof. exact (TRANS (@lem5443684) (@lem5443690)). Qed.
Lemma lem5443693 (x : nat) : (term710 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5443694 : term711 = term214.
Proof. exact (@lem5443693 term228). Qed.
Lemma lem5443695 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5443696 : term765 = term216.
Proof. exact (MK_COMB (@lem5443695) (@lem5443694)). Qed.
Lemma lem5443697 : term764 = term759.
Proof. exact (MK_COMB (@lem5443696) (@lem5443691)). Qed.
Lemma lem5443699 (m : nat) (n : nat) : (term766 m n) = (term767 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5443700 : term759 = term768.
Proof. exact (@lem5443699 (NUMERAL 0) term228). Qed.
Lemma lem5443701 : term707 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5443702 (h1 : term707 = (BIT1 0)) : (term228 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5443703 : (term707 = (BIT1 0)) = ((term228 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term707 = (BIT1 0) => @lem5443702 h1) (fun h1 : (term228 = (NUMERAL 0)) = False => @lem5443701)). Qed.
Lemma lem5443704 : (term228 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5443703) (@lem5443701)). Qed.
Lemma lem5443705 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5443706 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5443707 : term769 = (and True).
Proof. exact (MK_COMB (@lem5443706) (@lem5443705)). Qed.
Lemma lem5443708 : term768 = (True /\ False).
Proof. exact (MK_COMB (@lem5443707) (@lem5443704)). Qed.
Lemma lem5443710 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5443711 : term768 = False.
Proof. exact (TRANS (@lem5443708) (@lem5443710)). Qed.
Lemma lem5443712 : term759 = False.
Proof. exact (TRANS (@lem5443700) (@lem5443711)). Qed.
Lemma lem5443713 : term764 = False.
Proof. exact (TRANS (@lem5443697) (@lem5443712)). Qed.
Lemma lem5443714 : term761 = False.
Proof. exact (TRANS (@lem5443681) (@lem5443713)). Qed.
Lemma lem5443715 : term759 = False.
Proof. exact (TRANS (@lem5443658) (@lem5443714)). Qed.
Lemma lem5443716 : term758 = False.
Proof. exact (TRANS (@lem5443649) (@lem5443715)). Qed.
Lemma lem5443717 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term691 _70504 _70505 _70506 _70507 _70508) : False.
Proof. exact (EQ_MP (@lem5443716) (@lem5443646 _70504 _70505 _70506 _70507 _70508 h1)). Qed.
Lemma lem5443718 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term693 _70504 _70505 _70506 _70507 _70508) : False.
Proof. exact (or_elim (@lem5442763 _70504 _70505 _70506 _70507 _70508 h1) (fun h0 : term679 _70504 _70506 _70507 _70505 _70508 => @lem5443240 _70504 _70506 _70507 _70505 _70508 h0) (fun h0 : term691 _70504 _70505 _70506 _70507 _70508 => @lem5443717 _70504 _70505 _70506 _70507 _70508 h0)). Qed.
Lemma lem5443719 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term696 _70504 _70505 _70506 _70507 _70508) : False.
Proof. exact (or_elim (@lem5441806 _70504 _70505 _70506 _70507 _70508 h1) (fun h0 : term646 _70505 _70506 _70507 _70504 _70508 => @lem5442762 _70505 _70506 _70507 _70504 _70508 h0) (fun h0 : term693 _70504 _70505 _70506 _70507 _70508 => @lem5443718 _70504 _70505 _70506 _70507 _70508 h0)). Qed.
Lemma lem5443720 (_70504 : int) (_70505 : int) (_70506 : int) (_70507 : int) (_70508 : int) (h1 : term698 _70504 _70505 _70506 _70507 _70508) : False.
Proof. exact (or_elim (@lem5439899 _70504 _70505 _70506 _70507 _70508 h1) (fun h0 : term574 _70504 _70506 _70505 _70507 _70508 => @lem5441805 _70504 _70506 _70505 _70507 _70508 h0) (fun h0 : term696 _70504 _70505 _70506 _70507 _70508 => @lem5443719 _70504 _70505 _70506 _70507 _70508 h0)). Qed.
Lemma lem5443721 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) (h1 : term525 _70504 _70506 _70508 _70505 _70507) : term525 _70504 _70506 _70508 _70505 _70507.
Proof. exact (h1). Qed.
Lemma lem5443722 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) (h1 : term525 _70504 _70506 _70508 _70505 _70507) : term698 _70504 _70505 _70506 _70507 _70508.
Proof. exact (EQ_MP (@lem5439898 _70504 _70505 _70506 _70507 _70508) (@lem5443721 _70504 _70506 _70508 _70505 _70507 h1)). Qed.
Lemma lem5443723 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) (h1 : term525 _70504 _70506 _70508 _70505 _70507) : (term698 _70504 _70505 _70506 _70507 _70508) = False.
Proof. exact (prop_ext (fun h2 : term698 _70504 _70505 _70506 _70507 _70508 => @lem5443720 _70504 _70505 _70506 _70507 _70508 h2) (fun h2 : False => @lem5443722 _70504 _70506 _70508 _70505 _70507 h1)). Qed.
Lemma lem5443724 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) (h1 : term525 _70504 _70506 _70508 _70505 _70507) : False.
Proof. exact (EQ_MP (@lem5443723 _70504 _70506 _70508 _70505 _70507 h1) (@lem5443722 _70504 _70506 _70508 _70505 _70507 h1)). Qed.
Lemma lem5443725 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term286 _70504 _70506 _70505 _70507 _70508) : term286 _70504 _70506 _70505 _70507 _70508.
Proof. exact (h1). Qed.
Lemma lem5443726 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term286 _70504 _70506 _70505 _70507 _70508) : term525 _70504 _70506 _70508 _70505 _70507.
Proof. exact (EQ_MP (@lem5438467 _70504 _70506 _70508 _70505 _70507) (@lem5443725 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5443727 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term286 _70504 _70506 _70505 _70507 _70508) : (term525 _70504 _70506 _70508 _70505 _70507) = False.
Proof. exact (prop_ext (fun h2 : term525 _70504 _70506 _70508 _70505 _70507 => @lem5443724 _70504 _70506 _70508 _70505 _70507 h2) (fun h2 : False => @lem5443726 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5443728 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) (h1 : term286 _70504 _70506 _70505 _70507 _70508) : False.
Proof. exact (EQ_MP (@lem5443727 _70504 _70506 _70505 _70507 _70508 h1) (@lem5443726 _70504 _70506 _70505 _70507 _70508 h1)). Qed.
Lemma lem5443729 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : term788 _70504 _70506 _70505 _70507 _70508.
Proof. exact (fun h0 : term286 _70504 _70506 _70505 _70507 _70508 => @lem5443728 _70504 _70506 _70505 _70507 _70508 h0). Qed.
Lemma lem5443730 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : term789 _70504 _70506 _70505 _70507 _70508.
Proof. exact (@lem1386578 (term790 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5443733 (_70504 : int) (_70506 : int) (_70505 : int) (_70507 : int) (_70508 : int) : term790 _70504 _70506 _70505 _70507 _70508.
Proof. exact (@lem5443730 _70504 _70506 _70505 _70507 _70508 (@lem5443729 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5443734 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term284 _70504 _70506 _70505 _70507 _70508) = (term207 _70504 _70506 _70508 _70505 _70507).
Proof. exact (SYM (@lem5437196 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5443735 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5443736 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : (term790 _70504 _70506 _70505 _70507 _70508) = (term136 _70504 _70506 _70508 _70505 _70507).
Proof. exact (MK_COMB (@lem5443735) (@lem5443734 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5443737 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : term136 _70504 _70506 _70508 _70505 _70507.
Proof. exact (EQ_MP (@lem5443736 _70504 _70506 _70508 _70505 _70507) (@lem5443733 _70504 _70506 _70505 _70507 _70508)). Qed.
Lemma lem5443738 (_70504 : int) (_70506 : int) (_70508 : int) (_70505 : int) (_70507 : int) : term137 _70504 _70506 _70508 _70505 _70507.
Proof. exact (EQ_MP (@lem5436681 _70504 _70506 _70508 _70505 _70507) (@lem5443737 _70504 _70506 _70508 _70505 _70507)). Qed.
Lemma lem5443739 (m : nat) (p : nat) (x : nat) (n : nat) (q : nat) : term791 m p x n q.
Proof. exact (@lem5443738 (int_of_num m) (int_of_num p) (int_of_num x) (int_of_num n) (int_of_num q)). Qed.
Lemma lem5443740 (m : nat) (p : nat) (x : nat) (n : nat) (q : nat) : term792 m p x n q.
Proof. exact (@lem5443739 m p x n q (@lem5436668 m)). Qed.
Lemma lem5443741 (m : nat) (p : nat) (x : nat) (n : nat) (q : nat) : term793 m p x n q.
Proof. exact (@lem5443740 m p x n q (@lem5436671 n)). Qed.
Lemma lem5443742 (m : nat) (p : nat) (x : nat) (n : nat) (q : nat) : term794 m p x n q.
Proof. exact (@lem5443741 m p x n q (@lem5436674 p)). Qed.
Lemma lem5443743 (m : nat) (p : nat) (x : nat) (n : nat) (q : nat) : term795 m p x n q.
Proof. exact (@lem5443742 m p x n q (@lem5436677 q)). Qed.
Lemma lem5443744 (m : nat) (p : nat) (x : nat) (n : nat) (q : nat) : term123 m p x n q.
Proof. exact (@lem5443743 m p x n q (@lem5436680 x)). Qed.
Lemma lem5443745 (m : nat) (p : nat) (n : nat) (q : nat) : term125 m p n q.
Proof. exact (fun x : nat => @lem5443744 m p x n q). Qed.
Lemma lem5443746 (m : nat) (p : nat) (n : nat) : term127 m p n.
Proof. exact (fun q : nat => @lem5443745 m p n q). Qed.
Lemma lem5443747 (m : nat) (n : nat) : term129 m n.
Proof. exact (fun p : nat => @lem5443746 m p n). Qed.
Lemma lem5443748 (m : nat) : term131 m.
Proof. exact (fun n : nat => @lem5443747 m n). Qed.
Lemma lem5443749 : term133.
Proof. exact (fun m : nat => @lem5443748 m). Qed.
Lemma lem5443750 : term133 = term51.
Proof. exact (SYM (@lem5436665)). Qed.
Lemma lem5443751 : term51.
Proof. exact (EQ_MP (@lem5443750) (@lem5443749)). Qed.
Lemma lem5443752 : term51 = (term51 = True).
Proof. exact (@lem7 term51). Qed.
Lemma lem5443753 : term51 = True.
Proof. exact (EQ_MP (@lem5443752) (@lem5443751)). Qed.
Lemma lem5443754 : True = term51.
Proof. exact (SYM (@lem5443753)). Qed.
Lemma lem5443755 : term51.
Proof. exact (EQ_MP (@lem5443754) (@lem0)). Qed.
Lemma lem5443756 : term50.
Proof. exact (EQ_MP (@lem5436213) (@lem5443755)). Qed.
