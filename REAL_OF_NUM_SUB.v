Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_OF_NUM_SUB_term_abbrevs.
Require Import ADD_SUB2_spec.
Require Import DISJ_ACI_spec.
Require Import LE_EXISTS_spec.
Require Import real_sub_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1338238_spec.
Require Import thm1338438_spec.
Require Import thm1338512_spec.
Require Import thm1338588_spec.
Require Import thm1340339_spec.
Require Import thm16474_spec.
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
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Lemma lem1484082 (x : real) (y : real) (z : real) (h1 : (term0 x y z) = (term1 x y z)) : (term0 x y z) = (term1 x y z).
Proof. exact (h1). Qed.
Lemma lem1484083 (x : real) (y : real) (z : real) (h1 : (term0 x y z) = (term1 x y z)) : (term1 x y z) = (term0 x y z).
Proof. exact (SYM (@lem1484082 x y z h1)). Qed.
Lemma lem1484084 (x : real) (y : real) (z : real) (h1 : (term1 x y z) = (term0 x y z)) : (term1 x y z) = (term0 x y z).
Proof. exact (h1). Qed.
Lemma lem1484085 (x : real) (y : real) (z : real) (h1 : (term1 x y z) = (term0 x y z)) : (term0 x y z) = (term1 x y z).
Proof. exact (SYM (@lem1484084 x y z h1)). Qed.
Lemma lem1484086 (x : real) (y : real) (z : real) : ((term0 x y z) = (term1 x y z)) = ((term1 x y z) = (term0 x y z)).
Proof. exact (prop_ext (fun h1 : (term0 x y z) = (term1 x y z) => @lem1484083 x y z h1) (fun h1 : (term1 x y z) = (term0 x y z) => @lem1484085 x y z h1)). Qed.
Lemma lem1484087 (x : real) (y : real) : (term2 x y) = (term3 x y).
Proof. exact (fun_ext (fun z : real => @lem1484086 x y z)). Qed.
Lemma lem1484088 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1484089 (x : real) (y : real) : (term4 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1484088) (@lem1484087 x y)). Qed.
Lemma lem1484090 (x : real) : (term6 x) = (term7 x).
Proof. exact (fun_ext (fun y : real => @lem1484089 x y)). Qed.
Lemma lem1484091 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1484092 (x : real) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem1484091) (@lem1484090 x)). Qed.
Lemma lem1484093 : term10 = term11.
Proof. exact (fun_ext (fun x : real => @lem1484092 x)). Qed.
Lemma lem1484094 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1484095 : term12 = term13.
Proof. exact (MK_COMB (@lem1484094) (@lem1484093)). Qed.
Lemma lem1484096 : term13.
Proof. exact (EQ_MP (@lem1484095) (@lem1338438)). Qed.
Lemma lem1484097 (x : real) : term14 x.
Proof. exact (@lem1484096 x). Qed.
Lemma lem1484098 (x : real) : (term14 x) = (term9 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1484099 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1484098 x) (@lem1484097 x)). Qed.
Lemma lem1484100 (x : real) (y : real) : term15 x y.
Proof. exact (@lem1484099 x y). Qed.
Lemma lem1484101 (x : real) (y : real) : (term15 x y) = (term5 x y).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1484102 (x : real) (y : real) : term5 x y.
Proof. exact (EQ_MP (@lem1484101 x y) (@lem1484100 x y)). Qed.
Lemma lem1484103 (x : real) (y : real) (z : real) : term16 x y z.
Proof. exact (@lem1484102 x y z). Qed.
Lemma lem1484104 (x : real) (y : real) (z : real) : (term16 x y z) = ((term1 x y z) = (term0 x y z)).
Proof. exact (eq_refl (term16 x y z)). Qed.
Lemma lem1484106 (x : real) : term17 x.
Proof. exact (@lem1340977 x). Qed.
Lemma lem1484107 (x : real) : (term17 x) = (term18 x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem1484108 (x : real) : term18 x.
Proof. exact (EQ_MP (@lem1484107 x) (@lem1484106 x)). Qed.
Lemma lem1484109 (x : real) (y : real) : term19 x y.
Proof. exact (@lem1484108 x y). Qed.
Lemma lem1484110 (x : real) (y : real) : (term19 x y) = ((real_sub x y) = (term20 x y)).
Proof. exact (eq_refl (term19 x y)). Qed.
Lemma lem1484112 (x : real) : term21 x.
Proof. exact (@lem1338238 x). Qed.
Lemma lem1484113 (x : real) : (term21 x) = (term22 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1484114 (x : real) : term22 x.
Proof. exact (EQ_MP (@lem1484113 x) (@lem1484112 x)). Qed.
Lemma lem1484115 (x : real) (y : real) : term23 x y.
Proof. exact (@lem1484114 x y). Qed.
Lemma lem1484116 (y : real) (x : real) : (term23 x y) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem1484120 (m : nat) (n : nat) (h1 : (term24 m n) = (term25 m n)) : (term24 m n) = (term25 m n).
Proof. exact (h1). Qed.
Lemma lem1484121 (m : nat) (n : nat) (h1 : (term24 m n) = (term25 m n)) : (term25 m n) = (term24 m n).
Proof. exact (SYM (@lem1484120 m n h1)). Qed.
Lemma lem1484122 (m : nat) (n : nat) (h1 : (term25 m n) = (term24 m n)) : (term25 m n) = (term24 m n).
Proof. exact (h1). Qed.
Lemma lem1484123 (m : nat) (n : nat) (h1 : (term25 m n) = (term24 m n)) : (term24 m n) = (term25 m n).
Proof. exact (SYM (@lem1484122 m n h1)). Qed.
Lemma lem1484124 (m : nat) (n : nat) : ((term24 m n) = (term25 m n)) = ((term25 m n) = (term24 m n)).
Proof. exact (prop_ext (fun h1 : (term24 m n) = (term25 m n) => @lem1484121 m n h1) (fun h1 : (term25 m n) = (term24 m n) => @lem1484123 m n h1)). Qed.
Lemma lem1484125 (m : nat) : (term26 m) = (term27 m).
Proof. exact (fun_ext (fun n : nat => @lem1484124 m n)). Qed.
Lemma lem1484126 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1484127 (m : nat) : (term28 m) = (term29 m).
Proof. exact (MK_COMB (@lem1484126) (@lem1484125 m)). Qed.
Lemma lem1484128 : term30 = term31.
Proof. exact (fun_ext (fun m : nat => @lem1484127 m)). Qed.
Lemma lem1484129 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1484130 : term32 = term33.
Proof. exact (MK_COMB (@lem1484129) (@lem1484128)). Qed.
Lemma lem1484131 : term33.
Proof. exact (EQ_MP (@lem1484130) (@lem1340339)). Qed.
Lemma lem1484132 (m : nat) : term34 m.
Proof. exact (@lem1484131 m). Qed.
Lemma lem1484133 (m : nat) : (term34 m) = (term29 m).
Proof. exact (eq_refl (term34 m)). Qed.
Lemma lem1484134 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem1484133 m) (@lem1484132 m)). Qed.
Lemma lem1484135 (m : nat) (n : nat) : term35 m n.
Proof. exact (@lem1484134 m n). Qed.
Lemma lem1484136 (m : nat) (n : nat) : (term35 m n) = ((term25 m n) = (term24 m n)).
Proof. exact (eq_refl (term35 m n)). Qed.
Lemma lem1484138 (m : nat) : term36 m.
Proof. exact (@lem99708 m). Qed.
Lemma lem1484139 (m : nat) : (term36 m) = (term37 m).
Proof. exact (eq_refl (term36 m)). Qed.
Lemma lem1484140 (m : nat) : term37 m.
Proof. exact (EQ_MP (@lem1484139 m) (@lem1484138 m)). Qed.
Lemma lem1484141 (m : nat) (n : nat) : term38 m n.
Proof. exact (@lem1484140 m n). Qed.
Lemma lem1484142 (n : nat) (m : nat) : (term38 m n) = ((Peano.le m n) = (term39 n m)).
Proof. exact (eq_refl (term38 m n)). Qed.
Lemma lem1484147 (n : nat) (m : nat) : (Peano.le m n) = (term39 n m).
Proof. exact (EQ_MP (@lem1484142 n m) (@lem1484141 m n)). Qed.
Lemma lem1484154 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1484155 (n : nat) (m : nat) : (term40 m n) = (term41 n m).
Proof. exact (MK_COMB (@lem1484154) (@lem1484147 n m)). Qed.
Lemma lem1484158 (n : nat) (m : nat) : ((term42 n m) = (term43 n m)) = ((term42 n m) = (term43 n m)).
Proof. exact (eq_refl ((term42 n m) = (term43 n m))). Qed.
Lemma lem1484159 (n : nat) (m : nat) : (term44 n m) = (term45 n m).
Proof. exact (MK_COMB (@lem1484155 n m) (@lem1484158 n m)). Qed.
Lemma lem1484162 (n : nat) (m : nat) : (term45 n m) = (term44 n m).
Proof. exact (SYM (@lem1484159 n m)). Qed.
Lemma lem1484163 (n : nat) (m : nat) (h1 : term39 n m) : term39 n m.
Proof. exact (h1). Qed.
Lemma lem1484164 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : n = (Nat.add m d).
Proof. exact (h1). Qed.
Lemma lem1484165 (m : nat) : term46 m.
Proof. exact (@lem135939 m). Qed.
Lemma lem1484166 (m : nat) : (term46 m) = (term47 m).
Proof. exact (eq_refl (term46 m)). Qed.
Lemma lem1484167 (m : nat) : term47 m.
Proof. exact (EQ_MP (@lem1484166 m) (@lem1484165 m)). Qed.
Lemma lem1484168 (m : nat) (n : nat) : term48 m n.
Proof. exact (@lem1484167 m n). Qed.
Lemma lem1484169 (m : nat) (n : nat) : (term48 m n) = ((term49 n m) = n).
Proof. exact (eq_refl (term48 m n)). Qed.
Lemma lem1484174 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : n = (Nat.add m d).
Proof. exact (h1). Qed.
Lemma lem1484175 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1484176 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (real_of_num n) = (term25 m d).
Proof. exact (MK_COMB (@lem1484175) (@lem1484174 n m d h1)). Qed.
Lemma lem1484177 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1484178 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term50 n) = (term51 m d).
Proof. exact (MK_COMB (@lem1484177) (@lem1484176 n m d h1)). Qed.
Lemma lem1484179 (m : nat) : (real_of_num m) = (real_of_num m).
Proof. exact (eq_refl (real_of_num m)). Qed.
Lemma lem1484180 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term42 n m) = (term52 d m).
Proof. exact (MK_COMB (@lem1484178 n m d h1) (@lem1484179 m)). Qed.
Lemma lem1484181 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1484182 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term53 n m) = (term54 d m).
Proof. exact (MK_COMB (@lem1484181) (@lem1484180 n m d h1)). Qed.
Lemma lem1484184 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : n = (Nat.add m d).
Proof. exact (h1). Qed.
Lemma lem1484185 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem1484186 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (Nat.sub n) = (term55 m d).
Proof. exact (MK_COMB (@lem1484185) (@lem1484184 n m d h1)). Qed.
Lemma lem1484187 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1484188 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (Nat.sub n m) = (term49 d m).
Proof. exact (MK_COMB (@lem1484186 n m d h1) (@lem1484187 m)). Qed.
Lemma lem1484190 (m : nat) (n : nat) : (term49 n m) = n.
Proof. exact (EQ_MP (@lem1484169 m n) (@lem1484168 m n)). Qed.
Lemma lem1484191 (m : nat) (d : nat) : (term49 d m) = d.
Proof. exact (@lem1484190 m d). Qed.
Lemma lem1484192 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (Nat.sub n m) = d.
Proof. exact (TRANS (@lem1484188 n m d h1) (@lem1484191 m d)). Qed.
Lemma lem1484193 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1484194 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term43 n m) = (real_of_num d).
Proof. exact (MK_COMB (@lem1484193) (@lem1484192 n m d h1)). Qed.
Lemma lem1484195 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : ((term42 n m) = (term43 n m)) = ((term52 d m) = (real_of_num d)).
Proof. exact (MK_COMB (@lem1484182 n m d h1) (@lem1484194 n m d h1)). Qed.
Lemma lem1484198 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : ((term52 d m) = (real_of_num d)) = ((term42 n m) = (term43 n m)).
Proof. exact (SYM (@lem1484195 n m d h1)). Qed.
Lemma lem1484202 (m : nat) (n : nat) : (term25 m n) = (term24 m n).
Proof. exact (EQ_MP (@lem1484136 m n) (@lem1484135 m n)). Qed.
Lemma lem1484203 (m : nat) (d : nat) : (term25 m d) = (term24 m d).
Proof. exact (@lem1484202 m d). Qed.
Lemma lem1484204 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1484205 (m : nat) (d : nat) : (term51 m d) = (term56 m d).
Proof. exact (MK_COMB (@lem1484204) (@lem1484203 m d)). Qed.
Lemma lem1484206 (m : nat) : (real_of_num m) = (real_of_num m).
Proof. exact (eq_refl (real_of_num m)). Qed.
Lemma lem1484207 (d : nat) (m : nat) : (term52 d m) = (term57 d m).
Proof. exact (MK_COMB (@lem1484205 m d) (@lem1484206 m)). Qed.
Lemma lem1484208 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1484209 (d : nat) (m : nat) : (term54 d m) = (term58 d m).
Proof. exact (MK_COMB (@lem1484208) (@lem1484207 d m)). Qed.
Lemma lem1484210 (d : nat) : (real_of_num d) = (real_of_num d).
Proof. exact (eq_refl (real_of_num d)). Qed.
Lemma lem1484211 (m : nat) (d : nat) : ((term52 d m) = (real_of_num d)) = ((term57 d m) = (real_of_num d)).
Proof. exact (MK_COMB (@lem1484209 d m) (@lem1484210 d)). Qed.
Lemma lem1484214 (m : nat) (d : nat) : ((term57 d m) = (real_of_num d)) = ((term52 d m) = (real_of_num d)).
Proof. exact (SYM (@lem1484211 m d)). Qed.
Lemma lem1484218 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1484116 y x) (@lem1484115 x y)). Qed.
Lemma lem1484219 (d : nat) (m : nat) : (term24 m d) = (term24 d m).
Proof. exact (@lem1484218 (real_of_num d) (real_of_num m)). Qed.
Lemma lem1484220 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1484221 (d : nat) (m : nat) : (term56 m d) = (term56 d m).
Proof. exact (MK_COMB (@lem1484220) (@lem1484219 d m)). Qed.
Lemma lem1484222 (m : nat) : (real_of_num m) = (real_of_num m).
Proof. exact (eq_refl (real_of_num m)). Qed.
Lemma lem1484223 (d : nat) (m : nat) : (term57 d m) = (term59 d m).
Proof. exact (MK_COMB (@lem1484221 d m) (@lem1484222 m)). Qed.
Lemma lem1484224 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1484225 (d : nat) (m : nat) : (term58 d m) = (term60 d m).
Proof. exact (MK_COMB (@lem1484224) (@lem1484223 d m)). Qed.
Lemma lem1484226 (d : nat) : (real_of_num d) = (real_of_num d).
Proof. exact (eq_refl (real_of_num d)). Qed.
Lemma lem1484227 (m : nat) (d : nat) : ((term57 d m) = (real_of_num d)) = ((term59 d m) = (real_of_num d)).
Proof. exact (MK_COMB (@lem1484225 d m) (@lem1484226 d)). Qed.
Lemma lem1484228 (m : nat) (d : nat) : ((term59 d m) = (real_of_num d)) = ((term57 d m) = (real_of_num d)).
Proof. exact (SYM (@lem1484227 m d)). Qed.
Lemma lem1484232 (x : real) (y : real) : (real_sub x y) = (term20 x y).
Proof. exact (EQ_MP (@lem1484110 x y) (@lem1484109 x y)). Qed.
Lemma lem1484233 (d : nat) (m : nat) : (term59 d m) = (term61 d m).
Proof. exact (@lem1484232 (term24 d m) (real_of_num m)). Qed.
Lemma lem1484235 (x : real) (y : real) (z : real) : (term1 x y z) = (term0 x y z).
Proof. exact (EQ_MP (@lem1484104 x y z) (@lem1484103 x y z)). Qed.
Lemma lem1484236 (d : nat) (m : nat) : (term61 d m) = (term62 d m).
Proof. exact (@lem1484235 (real_of_num d) (real_of_num m) (term63 m)). Qed.
Lemma lem1484237 (d : nat) (m : nat) : (term59 d m) = (term62 d m).
Proof. exact (TRANS (@lem1484233 d m) (@lem1484236 d m)). Qed.
Lemma lem1484238 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1484239 (d : nat) (m : nat) : (term60 d m) = (term64 d m).
Proof. exact (MK_COMB (@lem1484238) (@lem1484237 d m)). Qed.
Lemma lem1484240 (d : nat) : (real_of_num d) = (real_of_num d).
Proof. exact (eq_refl (real_of_num d)). Qed.
Lemma lem1484241 (m : nat) (d : nat) : ((term59 d m) = (real_of_num d)) = ((term62 d m) = (real_of_num d)).
Proof. exact (MK_COMB (@lem1484239 d m) (@lem1484240 d)). Qed.
Lemma lem1484244 (m : nat) (d : nat) : ((term62 d m) = (real_of_num d)) = ((term59 d m) = (real_of_num d)).
Proof. exact (SYM (@lem1484241 m d)). Qed.
Lemma lem1484246 (p : Prop) : p = (term65 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1484247 (m : nat) (d : nat) : ((term62 d m) = (real_of_num d)) = (term66 m d).
Proof. exact (@lem1484246 ((term62 d m) = (real_of_num d))). Qed.
Lemma lem1484248 (m : nat) (d : nat) : (term66 m d) = ((term62 d m) = (real_of_num d)).
Proof. exact (SYM (@lem1484247 m d)). Qed.
Lemma lem1484249 (m : nat) (d : nat) (h1 : term67 m d) : term67 m d.
Proof. exact (h1). Qed.
Lemma lem1484252 (m : nat) (d : nat) (h1 : term68 m d) : term68 m d.
Proof. exact (h1). Qed.
Lemma lem1484253 (m : nat) (d : nat) : term69 m d.
Proof. exact (fun h0 : term68 m d => @lem1484252 m d h0). Qed.
Lemma lem1484254 (m : nat) (d : nat) (h1 : term69 m d) : term69 m d.
Proof. exact (h1). Qed.
Lemma lem1484255 (m : nat) (d : nat) (h1 : term68 m d) : term68 m d.
Proof. exact (h1). Qed.
Lemma lem1484256 (m : nat) (d : nat) (h1 : term68 m d) (h2 : term69 m d) : term68 m d.
Proof. exact (@lem1484254 m d h2 (@lem1484255 m d h1)). Qed.
Lemma lem1484257 (m : nat) (d : nat) (h1 : term68 m d) : term70 m d.
Proof. exact (fun h0 : term69 m d => @lem1484256 m d h1 h0). Qed.
Lemma lem1484258 (m : nat) (d : nat) (h1 : term69 m d) : term69 m d.
Proof. exact (h1). Qed.
Lemma lem1484259 (m : nat) (d : nat) (h1 : term68 m d) (h2 : term69 m d) : term68 m d.
Proof. exact (@lem1484257 m d h1 (@lem1484258 m d h2)). Qed.
Lemma lem1484260 (m : nat) (d : nat) (h1 : term69 m d) : term69 m d.
Proof. exact (fun h0 : term68 m d => @lem1484259 m d h0 h1). Qed.
Lemma lem1484261 (m : nat) (d : nat) : term71 m d.
Proof. exact (fun h0 : term69 m d => @lem1484260 m d h0). Qed.
Lemma lem1484264 (m : nat) (d : nat) : term69 m d.
Proof. exact (@lem1484261 m d (@lem1484253 m d)). Qed.
Lemma lem1484292 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1484293 : term72 = term73.
Proof. exact (@lem1484292 term74). Qed.
Lemma lem1484298 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1484299 : term76 = term77.
Proof. exact (MK_COMB (@lem1484298) (@lem1484293)). Qed.
Lemma lem1484302 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem1484303 : term79 = term80.
Proof. exact (MK_COMB (@lem1484302) (@lem1484299)). Qed.
Lemma lem1484306 (m : nat) (d : nat) : (term81 m d) = (term81 m d).
Proof. exact (eq_refl (term81 m d)). Qed.
Lemma lem1484307 (m : nat) (d : nat) : (term68 m d) = (term82 m d).
Proof. exact (MK_COMB (@lem1484306 m d) (@lem1484303)). Qed.
Lemma lem1484310 (d : nat) : (term83 d) = (term84 d).
Proof. exact (fun_ext (fun m : nat => @lem1484307 m d)). Qed.
Lemma lem1484311 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1484312 (d : nat) : (term85 d) = (term86 d).
Proof. exact (MK_COMB (@lem1484311) (@lem1484310 d)). Qed.
Lemma lem1484317 : term87 = term88.
Proof. exact (fun_ext (fun d : nat => @lem1484312 d)). Qed.
Lemma lem1484318 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1484327 : term89 = term90.
Proof. exact (MK_COMB (@lem1484318) (@lem1484317)). Qed.
Lemma lem1484328 (x : real) : ((term91 x) = term92) = ((term91 x) = term92).
Proof. exact (eq_refl ((term91 x) = term92)). Qed.
Lemma lem1484329 : term93 = term93.
Proof. exact (fun_ext (fun x : real => @lem1484328 x)). Qed.
Lemma lem1484330 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1484331 : term74 = term74.
Proof. exact (MK_COMB (@lem1484330) (@lem1484329)). Qed.
Lemma lem1484332 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1484333 : term73 = term73.
Proof. exact (MK_COMB (@lem1484332) (@lem1484331)). Qed.
Lemma lem1484334 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1484335 (x : real) : (term94 x) = (term94 x).
Proof. exact (fun_ext (fun y : real => @lem1484334 y x)). Qed.
Lemma lem1484336 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1484337 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1484336) (@lem1484335 x)). Qed.
Lemma lem1484338 : term95 = term95.
Proof. exact (fun_ext (fun x : real => @lem1484337 x)). Qed.
Lemma lem1484339 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1484340 : term96 = term96.
Proof. exact (MK_COMB (@lem1484339) (@lem1484338)). Qed.
Lemma lem1484341 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1484342 : term75 = term75.
Proof. exact (MK_COMB (@lem1484341) (@lem1484340)). Qed.
Lemma lem1484343 : term77 = term77.
Proof. exact (MK_COMB (@lem1484342) (@lem1484333)). Qed.
Lemma lem1484344 (x : real) : ((term97 x) = x) = ((term97 x) = x).
Proof. exact (eq_refl ((term97 x) = x)). Qed.
Lemma lem1484345 : term98 = term98.
Proof. exact (fun_ext (fun x : real => @lem1484344 x)). Qed.
Lemma lem1484346 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1484347 : term99 = term99.
Proof. exact (MK_COMB (@lem1484346) (@lem1484345)). Qed.
Lemma lem1484348 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1484349 : term78 = term78.
Proof. exact (MK_COMB (@lem1484348) (@lem1484347)). Qed.
Lemma lem1484350 : term80 = term80.
Proof. exact (MK_COMB (@lem1484349) (@lem1484343)). Qed.
Lemma lem1484355 (m : nat) (d : nat) : (term81 m d) = (term81 m d).
Proof. exact (eq_refl (term81 m d)). Qed.
Lemma lem1484356 (m : nat) (d : nat) : (term82 m d) = (term82 m d).
Proof. exact (MK_COMB (@lem1484355 m d) (@lem1484350)). Qed.
Lemma lem1484357 (d : nat) : (term84 d) = (term84 d).
Proof. exact (fun_ext (fun m : nat => @lem1484356 m d)). Qed.
Lemma lem1484358 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1484359 (d : nat) : (term86 d) = (term86 d).
Proof. exact (MK_COMB (@lem1484358) (@lem1484357 d)). Qed.
Lemma lem1484360 : term88 = term88.
Proof. exact (fun_ext (fun d : nat => @lem1484359 d)). Qed.
Lemma lem1484361 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1484362 : term90 = term90.
Proof. exact (MK_COMB (@lem1484361) (@lem1484360)). Qed.
Lemma lem1484407 : term89 = term90.
Proof. exact (TRANS (@lem1484327) (@lem1484362)). Qed.
Lemma lem1484408 : term90 = term89.
Proof. exact (SYM (@lem1484407)). Qed.
Lemma lem1484410 (h1 : term99) : term99.
Proof. exact (h1). Qed.
Lemma lem1484411 (h1 : term96) : term96.
Proof. exact (h1). Qed.
Lemma lem1484412 (h1 : term74) : term74.
Proof. exact (h1). Qed.
Lemma lem1484418 (m : nat) (d : nat) (h1 : term67 m d) : term67 m d.
Proof. exact (h1). Qed.
Lemma lem1484419 (x : real) : ((term97 x) = x) = ((term97 x) = x).
Proof. exact (eq_refl ((term97 x) = x)). Qed.
Lemma lem1484420 : term98 = term98.
Proof. exact (fun_ext (fun x : real => @lem1484419 x)). Qed.
Lemma lem1484421 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1484430 : term99 = term99.
Proof. exact (MK_COMB (@lem1484421) (@lem1484420)). Qed.
Lemma lem1484431 (h1 : term99) : term99.
Proof. exact (EQ_MP (@lem1484430) (@lem1484410 h1)). Qed.
Lemma lem1484432 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1484433 (x : real) : (term94 x) = (term94 x).
Proof. exact (fun_ext (fun y : real => @lem1484432 y x)). Qed.
Lemma lem1484434 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1484435 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1484434) (@lem1484433 x)). Qed.
Lemma lem1484436 : term95 = term95.
Proof. exact (fun_ext (fun x : real => @lem1484435 x)). Qed.
Lemma lem1484437 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1484450 : term96 = term96.
Proof. exact (MK_COMB (@lem1484437) (@lem1484436)). Qed.
Lemma lem1484451 (h1 : term96) : term96.
Proof. exact (EQ_MP (@lem1484450) (@lem1484411 h1)). Qed.
Lemma lem1484452 (x : real) : ((term91 x) = term92) = ((term91 x) = term92).
Proof. exact (eq_refl ((term91 x) = term92)). Qed.
Lemma lem1484453 : term93 = term93.
Proof. exact (fun_ext (fun x : real => @lem1484452 x)). Qed.
Lemma lem1484454 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1484463 : term74 = term74.
Proof. exact (MK_COMB (@lem1484454) (@lem1484453)). Qed.
Lemma lem1484464 (h1 : term74) : term74.
Proof. exact (EQ_MP (@lem1484463) (@lem1484412 h1)). Qed.
Lemma lem1484490 (m : nat) (d : nat) (h1 : term67 m d) : term67 m d.
Proof. exact (h1). Qed.
Lemma lem1484503 (x : real) : ((term97 x) = x) = ((term97 x) = x).
Proof. exact (eq_refl ((term97 x) = x)). Qed.
Lemma lem1484504 : term98 = term98.
Proof. exact (fun_ext (fun x : real => @lem1484503 x)). Qed.
Lemma lem1484505 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1484506 : term99 = term99.
Proof. exact (MK_COMB (@lem1484505) (@lem1484504)). Qed.
Lemma lem1484507 (h1 : term99) : term99.
Proof. exact (EQ_MP (@lem1484506) (@lem1484431 h1)). Qed.
Lemma lem1484520 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1484521 (x : real) : (term94 x) = (term94 x).
Proof. exact (fun_ext (fun y : real => @lem1484520 y x)). Qed.
Lemma lem1484522 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1484523 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1484522) (@lem1484521 x)). Qed.
Lemma lem1484524 : term95 = term95.
Proof. exact (fun_ext (fun x : real => @lem1484523 x)). Qed.
Lemma lem1484525 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1484526 : term96 = term96.
Proof. exact (MK_COMB (@lem1484525) (@lem1484524)). Qed.
Lemma lem1484527 (h1 : term96) : term96.
Proof. exact (EQ_MP (@lem1484526) (@lem1484451 h1)). Qed.
Lemma lem1484542 (x : real) : ((term91 x) = term92) = ((term91 x) = term92).
Proof. exact (eq_refl ((term91 x) = term92)). Qed.
Lemma lem1484543 : term93 = term93.
Proof. exact (fun_ext (fun x : real => @lem1484542 x)). Qed.
Lemma lem1484544 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1484545 : term74 = term74.
Proof. exact (MK_COMB (@lem1484544) (@lem1484543)). Qed.
Lemma lem1484546 (h1 : term74) : term74.
Proof. exact (EQ_MP (@lem1484545) (@lem1484464 h1)). Qed.
Lemma lem1484550 (m : nat) (d : nat) (h1 : term67 m d) : term67 m d.
Proof. exact (h1). Qed.
Lemma lem1484552 (x : real) : ((term97 x) = x) = ((term97 x) = x).
Proof. exact (eq_refl ((term97 x) = x)). Qed.
Lemma lem1484553 : term98 = term98.
Proof. exact (fun_ext (fun x : real => @lem1484552 x)). Qed.
Lemma lem1484554 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1484556 : term99 = term99.
Proof. exact (MK_COMB (@lem1484554) (@lem1484553)). Qed.
Lemma lem1484557 (h1 : term99) : term99.
Proof. exact (EQ_MP (@lem1484556) (@lem1484507 h1)). Qed.
Lemma lem1484559 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1484560 (x : real) : (term94 x) = (term94 x).
Proof. exact (fun_ext (fun y : real => @lem1484559 y x)). Qed.
Lemma lem1484561 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1484562 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1484561) (@lem1484560 x)). Qed.
Lemma lem1484563 : term95 = term95.
Proof. exact (fun_ext (fun x : real => @lem1484562 x)). Qed.
Lemma lem1484564 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1484566 : term96 = term96.
Proof. exact (MK_COMB (@lem1484564) (@lem1484563)). Qed.
Lemma lem1484567 (h1 : term96) : term96.
Proof. exact (EQ_MP (@lem1484566) (@lem1484527 h1)). Qed.
Lemma lem1484569 (x : real) : ((term91 x) = term92) = ((term91 x) = term92).
Proof. exact (eq_refl ((term91 x) = term92)). Qed.
Lemma lem1484570 : term93 = term93.
Proof. exact (fun_ext (fun x : real => @lem1484569 x)). Qed.
Lemma lem1484571 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1484573 : term74 = term74.
Proof. exact (MK_COMB (@lem1484571) (@lem1484570)). Qed.
Lemma lem1484574 (h1 : term74) : term74.
Proof. exact (EQ_MP (@lem1484573) (@lem1484546 h1)). Qed.
Lemma lem1484575 (_24808 : real) (h1 : term99) : term100 _24808.
Proof. exact (@lem1484557 h1 _24808). Qed.
Lemma lem1484576 (_24808 : real) : (term100 _24808) = ((term97 _24808) = _24808).
Proof. exact (eq_refl (term100 _24808)). Qed.
Lemma lem1484578 (_24809 : real) (h1 : term96) : term21 _24809.
Proof. exact (@lem1484567 h1 _24809). Qed.
Lemma lem1484579 (_24809 : real) : (term21 _24809) = (term22 _24809).
Proof. exact (eq_refl (term21 _24809)). Qed.
Lemma lem1484580 (_24809 : real) (h1 : term96) : term22 _24809.
Proof. exact (EQ_MP (@lem1484579 _24809) (@lem1484578 _24809 h1)). Qed.
Lemma lem1484581 (_24809 : real) (_24810 : real) (h1 : term96) : term23 _24809 _24810.
Proof. exact (@lem1484580 _24809 h1 _24810). Qed.
Lemma lem1484582 (_24810 : real) (_24809 : real) : (term23 _24809 _24810) = ((real_add _24809 _24810) = (real_add _24810 _24809)).
Proof. exact (eq_refl (term23 _24809 _24810)). Qed.
Lemma lem1484584 (_24811 : real) (h1 : term74) : term101 _24811.
Proof. exact (@lem1484574 h1 _24811). Qed.
Lemma lem1484585 (_24811 : real) : (term101 _24811) = ((term91 _24811) = term92).
Proof. exact (eq_refl (term101 _24811)). Qed.
Lemma lem1484588 (m : nat) (d : nat) (h1 : term67 m d) : term67 m d.
Proof. exact (h1). Qed.
Lemma lem1484611 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1484612 (_24816 : real) (_24818 : real) (h1 : _24816 = _24818) : _24816 = _24818.
Proof. exact (h1). Qed.
Lemma lem1484613 (_24817 : real) (_24819 : real) (h1 : _24817 = _24819) : _24817 = _24819.
Proof. exact (h1). Qed.
Lemma lem1484614 (_24816 : real) (_24818 : real) (h1 : _24816 = _24818) : (real_add _24816) = (real_add _24818).
Proof. exact (MK_COMB (@lem1484611) (@lem1484612 _24816 _24818 h1)). Qed.
Lemma lem1484615 (_24816 : real) (_24818 : real) (_24817 : real) (_24819 : real) (h1 : _24816 = _24818) (h2 : _24817 = _24819) : (real_add _24816 _24817) = (real_add _24818 _24819).
Proof. exact (MK_COMB (@lem1484614 _24816 _24818 h1) (@lem1484613 _24817 _24819 h2)). Qed.
Lemma lem1484616 (_24817 : real) (_24819 : real) (_24816 : real) (_24818 : real) (h1 : _24816 = _24818) : term102 _24816 _24817 _24818 _24819.
Proof. exact (fun h0 : _24817 = _24819 => @lem1484615 _24816 _24818 _24817 _24819 h1 h0). Qed.
Lemma lem1484618 (a : Prop) (b : Prop) : (a -> b) = (term103 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1484619 (_24816 : real) (_24817 : real) (_24818 : real) (_24819 : real) : (term102 _24816 _24817 _24818 _24819) = (term104 _24816 _24817 _24818 _24819).
Proof. exact (@lem1484618 (_24817 = _24819) ((real_add _24816 _24817) = (real_add _24818 _24819))). Qed.
Lemma lem1484620 (_24817 : real) (_24819 : real) (_24816 : real) (_24818 : real) (h1 : _24816 = _24818) : term104 _24816 _24817 _24818 _24819.
Proof. exact (EQ_MP (@lem1484619 _24816 _24817 _24818 _24819) (@lem1484616 _24817 _24819 _24816 _24818 h1)). Qed.
Lemma lem1484621 (_24816 : real) (_24817 : real) (_24818 : real) (_24819 : real) : term105 _24816 _24817 _24818 _24819.
Proof. exact (fun h0 : _24816 = _24818 => @lem1484620 _24817 _24819 _24816 _24818 h0). Qed.
Lemma lem1484623 (a : Prop) (b : Prop) : (a -> b) = (term103 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1484624 (_24816 : real) (_24817 : real) (_24818 : real) (_24819 : real) : (term105 _24816 _24817 _24818 _24819) = (term106 _24816 _24817 _24818 _24819).
Proof. exact (@lem1484623 (_24816 = _24818) (term104 _24816 _24817 _24818 _24819)). Qed.
Lemma lem1484625 (_24816 : real) (_24817 : real) (_24818 : real) (_24819 : real) : term106 _24816 _24817 _24818 _24819.
Proof. exact (EQ_MP (@lem1484624 _24816 _24817 _24818 _24819) (@lem1484621 _24816 _24817 _24818 _24819)). Qed.
Lemma lem1484635 (x : real) (y : real) (z : real) : term107 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1484639 (_24810 : real) (_24809 : real) (h1 : term96) : (real_add _24809 _24810) = (real_add _24810 _24809).
Proof. exact (EQ_MP (@lem1484582 _24810 _24809) (@lem1484581 _24809 _24810 h1)). Qed.
Lemma lem1484640 (d : nat) (m : nat) (h1 : term96) : (term108 m d) = (term62 d m).
Proof. exact (@lem1484639 (real_of_num d) (term109 m) h1). Qed.
Lemma lem1484641 (d : nat) (m : nat) (h1 : term96) : term110 d m.
Proof. exact (fun h0 : term111 d m => @lem1484640 d m h1). Qed.
Lemma lem1484643 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1484644 (d : nat) (m : nat) : (term110 d m) = ((term108 m d) = (term62 d m)).
Proof. exact (@lem1484643 ((term108 m d) = (term62 d m))). Qed.
Lemma lem1484645 (d : nat) (m : nat) (h1 : term96) : (term108 m d) = (term62 d m).
Proof. exact (EQ_MP (@lem1484644 d m) (@lem1484641 d m h1)). Qed.
Lemma lem1484647 (_24811 : real) (h1 : term74) : (term91 _24811) = term92.
Proof. exact (EQ_MP (@lem1484585 _24811) (@lem1484584 _24811 h1)). Qed.
Lemma lem1484648 (m : nat) (h1 : term74) : (term113 m) = term92.
Proof. exact (@lem1484647 (real_of_num m) h1). Qed.
Lemma lem1484649 (m : nat) (h1 : term74) : term114 m.
Proof. exact (fun h0 : term115 m => @lem1484648 m h1). Qed.
Lemma lem1484651 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1484652 (m : nat) : (term114 m) = ((term113 m) = term92).
Proof. exact (@lem1484651 ((term113 m) = term92)). Qed.
Lemma lem1484653 (m : nat) (h1 : term74) : (term113 m) = term92.
Proof. exact (EQ_MP (@lem1484652 m) (@lem1484649 m h1)). Qed.
Lemma lem1484655 (_24810 : real) (_24809 : real) (h1 : term96) : (real_add _24809 _24810) = (real_add _24810 _24809).
Proof. exact (EQ_MP (@lem1484582 _24810 _24809) (@lem1484581 _24809 _24810 h1)). Qed.
Lemma lem1484656 (m : nat) (h1 : term96) : (term113 m) = (term109 m).
Proof. exact (@lem1484655 (real_of_num m) (term63 m) h1). Qed.
Lemma lem1484657 (m : nat) (h1 : term96) : term116 m.
Proof. exact (fun h0 : term117 m => @lem1484656 m h1). Qed.
Lemma lem1484659 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1484660 (m : nat) : (term116 m) = ((term113 m) = (term109 m)).
Proof. exact (@lem1484659 ((term113 m) = (term109 m))). Qed.
Lemma lem1484661 (m : nat) (h1 : term96) : (term113 m) = (term109 m).
Proof. exact (EQ_MP (@lem1484660 m) (@lem1484657 m h1)). Qed.
Lemma lem1484679 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1484680 (y : real) (x : real) (z : real) : (term118 x y z) = (term119 y x z).
Proof. exact (@lem1484679 (y = z) (term120 x z)). Qed.
Lemma lem1484690 (x : real) (y : real) : (term121 x y) = (term121 x y).
Proof. exact (eq_refl (term121 x y)). Qed.
Lemma lem1484691 (y : real) (x : real) (z : real) : (term107 x y z) = (term122 y x z).
Proof. exact (MK_COMB (@lem1484690 x y) (@lem1484680 y x z)). Qed.
Lemma lem1484695 (q : Prop) (p : Prop) (r : Prop) : (term123 p q r) = (term123 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1484696 (y : real) (x : real) (z : real) : (term122 y x z) = (term124 y x z).
Proof. exact (@lem1484695 (y = z) (term120 x y) (term120 x z)). Qed.
Lemma lem1484718 (y : real) (x : real) (z : real) : (term107 x y z) = (term124 y x z).
Proof. exact (TRANS (@lem1484691 y x z) (@lem1484696 y x z)). Qed.
Lemma lem1484719 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1484720 (y : real) (x : real) (z : real) : (term125 x y z) = (term126 y x z).
Proof. exact (MK_COMB (@lem1484719) (@lem1484718 y x z)). Qed.
Lemma lem1484742 (y : real) (x : real) (z : real) : (term124 y x z) = (term124 y x z).
Proof. exact (eq_refl (term124 y x z)). Qed.
Lemma lem1484743 (y : real) (x : real) (z : real) : ((term107 x y z) = (term124 y x z)) = ((term124 y x z) = (term124 y x z)).
Proof. exact (MK_COMB (@lem1484720 y x z) (@lem1484742 y x z)). Qed.
Lemma lem1484745 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1484746 (x : Prop) : (x = x) = True.
Proof. exact (@lem1484745 Prop x). Qed.
Lemma lem1484747 (y : real) (x : real) (z : real) : ((term124 y x z) = (term124 y x z)) = True.
Proof. exact (@lem1484746 (term124 y x z)). Qed.
Lemma lem1484748 (y : real) (x : real) (z : real) : ((term107 x y z) = (term124 y x z)) = True.
Proof. exact (TRANS (@lem1484743 y x z) (@lem1484747 y x z)). Qed.
Lemma lem1484749 (y : real) (x : real) (z : real) : True = ((term107 x y z) = (term124 y x z)).
Proof. exact (SYM (@lem1484748 y x z)). Qed.
Lemma lem1484750 (y : real) (x : real) (z : real) : (term107 x y z) = (term124 y x z).
Proof. exact (EQ_MP (@lem1484749 y x z) (@lem0)). Qed.
Lemma lem1484751 (y : real) (x : real) (z : real) : term124 y x z.
Proof. exact (EQ_MP (@lem1484750 y x z) (@lem1484635 x y z)). Qed.
Lemma lem1484753 (b : Prop) (a : Prop) : (a \/ b) = (term127 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1484754 (x : real) (y : real) (z : real) : (term124 y x z) = (term128 x y z).
Proof. exact (@lem1484753 (term129 y x z) (y = z)). Qed.
Lemma lem1484756 (a : Prop) (b : Prop) : (term130 a b) = (term131 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1484757 (y : real) (x : real) (z : real) : (term132 y x z) = (term133 y x z).
Proof. exact (@lem1484756 (term120 x y) (term120 x z)). Qed.
Lemma lem1484759 (a : Prop) : (term134 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1484760 (x : real) (y : real) : (term135 x y) = (x = y).
Proof. exact (@lem1484759 (x = y)). Qed.
Lemma lem1484761 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1484762 (x : real) (y : real) : (term136 x y) = (term137 x y).
Proof. exact (MK_COMB (@lem1484761) (@lem1484760 x y)). Qed.
Lemma lem1484764 (a : Prop) : (term134 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1484765 (x : real) (z : real) : (term135 x z) = (x = z).
Proof. exact (@lem1484764 (x = z)). Qed.
Lemma lem1484766 (y : real) (x : real) (z : real) : (term133 y x z) = (term138 y x z).
Proof. exact (MK_COMB (@lem1484762 x y) (@lem1484765 x z)). Qed.
Lemma lem1484767 (y : real) (x : real) (z : real) : (term132 y x z) = (term138 y x z).
Proof. exact (TRANS (@lem1484757 y x z) (@lem1484766 y x z)). Qed.
Lemma lem1484768 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1484769 (y : real) (x : real) (z : real) : (term139 y x z) = (term140 y x z).
Proof. exact (MK_COMB (@lem1484768) (@lem1484767 y x z)). Qed.
Lemma lem1484770 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1484771 (x : real) (y : real) (z : real) : (term128 x y z) = (term141 x y z).
Proof. exact (MK_COMB (@lem1484769 y x z) (@lem1484770 y z)). Qed.
Lemma lem1484772 (x : real) (y : real) (z : real) : (term124 y x z) = (term141 x y z).
Proof. exact (TRANS (@lem1484754 x y z) (@lem1484771 x y z)). Qed.
Lemma lem1484774 (m : nat) (h1 : term96) (h2 : term74) : term142 m.
Proof. exact (conj (@lem1484653 m h2) (@lem1484661 m h1)). Qed.
Lemma lem1484776 (x : real) (y : real) (z : real) : term141 x y z.
Proof. exact (EQ_MP (@lem1484772 x y z) (@lem1484751 y x z)). Qed.
Lemma lem1484777 (m : nat) : term143 m.
Proof. exact (@lem1484776 (term113 m) term92 (term109 m)). Qed.
Lemma lem1484780 (m : nat) (h1 : term96) (h2 : term74) : term92 = (term109 m).
Proof. exact (@lem1484777 m (@lem1484774 m h1 h2)). Qed.
Lemma lem1484781 (m : nat) (h1 : term96) (h2 : term74) : term144 m.
Proof. exact (fun h0 : term145 m => @lem1484780 m h1 h2). Qed.
Lemma lem1484783 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1484784 (m : nat) : (term144 m) = (term92 = (term109 m)).
Proof. exact (@lem1484783 (term92 = (term109 m))). Qed.
Lemma lem1484785 (m : nat) (h1 : term96) (h2 : term74) : term92 = (term109 m).
Proof. exact (EQ_MP (@lem1484784 m) (@lem1484781 m h1 h2)). Qed.
Lemma lem1484787 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1484788 (d : nat) : (real_of_num d) = (real_of_num d).
Proof. exact (@lem1484787 (real_of_num d)). Qed.
Lemma lem1484789 (d : nat) : term146 d.
Proof. exact (fun h0 : term147 d => @lem1484788 d). Qed.
Lemma lem1484791 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1484792 (d : nat) : (term146 d) = ((real_of_num d) = (real_of_num d)).
Proof. exact (@lem1484791 ((real_of_num d) = (real_of_num d))). Qed.
Lemma lem1484793 (d : nat) : (real_of_num d) = (real_of_num d).
Proof. exact (EQ_MP (@lem1484792 d) (@lem1484789 d)). Qed.
Lemma lem1484811 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1484812 (_24816 : real) (_24818 : real) (_24817 : real) (_24819 : real) : (term104 _24816 _24817 _24818 _24819) = (term148 _24816 _24818 _24817 _24819).
Proof. exact (@lem1484811 ((real_add _24816 _24817) = (real_add _24818 _24819)) (term120 _24817 _24819)). Qed.
Lemma lem1484822 (_24816 : real) (_24818 : real) : (term121 _24816 _24818) = (term121 _24816 _24818).
Proof. exact (eq_refl (term121 _24816 _24818)). Qed.
Lemma lem1484823 (_24816 : real) (_24818 : real) (_24817 : real) (_24819 : real) : (term106 _24816 _24817 _24818 _24819) = (term149 _24816 _24818 _24817 _24819).
Proof. exact (MK_COMB (@lem1484822 _24816 _24818) (@lem1484812 _24816 _24818 _24817 _24819)). Qed.
Lemma lem1484827 (q : Prop) (p : Prop) (r : Prop) : (term123 p q r) = (term123 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1484828 (_24816 : real) (_24818 : real) (_24817 : real) (_24819 : real) : (term149 _24816 _24818 _24817 _24819) = (term150 _24816 _24818 _24817 _24819).
Proof. exact (@lem1484827 ((real_add _24816 _24817) = (real_add _24818 _24819)) (term120 _24816 _24818) (term120 _24817 _24819)). Qed.
Lemma lem1484850 (_24816 : real) (_24818 : real) (_24817 : real) (_24819 : real) : (term106 _24816 _24817 _24818 _24819) = (term150 _24816 _24818 _24817 _24819).
Proof. exact (TRANS (@lem1484823 _24816 _24818 _24817 _24819) (@lem1484828 _24816 _24818 _24817 _24819)). Qed.
Lemma lem1484851 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1484852 (_24816 : real) (_24818 : real) (_24817 : real) (_24819 : real) : (term151 _24816 _24817 _24818 _24819) = (term152 _24816 _24818 _24817 _24819).
Proof. exact (MK_COMB (@lem1484851) (@lem1484850 _24816 _24818 _24817 _24819)). Qed.
Lemma lem1484874 (_24816 : real) (_24818 : real) (_24817 : real) (_24819 : real) : (term150 _24816 _24818 _24817 _24819) = (term150 _24816 _24818 _24817 _24819).
Proof. exact (eq_refl (term150 _24816 _24818 _24817 _24819)). Qed.
Lemma lem1484875 (_24816 : real) (_24818 : real) (_24817 : real) (_24819 : real) : ((term106 _24816 _24817 _24818 _24819) = (term150 _24816 _24818 _24817 _24819)) = ((term150 _24816 _24818 _24817 _24819) = (term150 _24816 _24818 _24817 _24819)).
Proof. exact (MK_COMB (@lem1484852 _24816 _24818 _24817 _24819) (@lem1484874 _24816 _24818 _24817 _24819)). Qed.
Lemma lem1484877 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1484878 (x : Prop) : (x = x) = True.
Proof. exact (@lem1484877 Prop x). Qed.
Lemma lem1484879 (_24816 : real) (_24818 : real) (_24817 : real) (_24819 : real) : ((term150 _24816 _24818 _24817 _24819) = (term150 _24816 _24818 _24817 _24819)) = True.
Proof. exact (@lem1484878 (term150 _24816 _24818 _24817 _24819)). Qed.
Lemma lem1484880 (_24816 : real) (_24818 : real) (_24817 : real) (_24819 : real) : ((term106 _24816 _24817 _24818 _24819) = (term150 _24816 _24818 _24817 _24819)) = True.
Proof. exact (TRANS (@lem1484875 _24816 _24818 _24817 _24819) (@lem1484879 _24816 _24818 _24817 _24819)). Qed.
Lemma lem1484881 (_24816 : real) (_24818 : real) (_24817 : real) (_24819 : real) : True = ((term106 _24816 _24817 _24818 _24819) = (term150 _24816 _24818 _24817 _24819)).
Proof. exact (SYM (@lem1484880 _24816 _24818 _24817 _24819)). Qed.
Lemma lem1484882 (_24816 : real) (_24818 : real) (_24817 : real) (_24819 : real) : (term106 _24816 _24817 _24818 _24819) = (term150 _24816 _24818 _24817 _24819).
Proof. exact (EQ_MP (@lem1484881 _24816 _24818 _24817 _24819) (@lem0)). Qed.
Lemma lem1484883 (_24816 : real) (_24818 : real) (_24817 : real) (_24819 : real) : term150 _24816 _24818 _24817 _24819.
Proof. exact (EQ_MP (@lem1484882 _24816 _24818 _24817 _24819) (@lem1484625 _24816 _24817 _24818 _24819)). Qed.
Lemma lem1484885 (b : Prop) (a : Prop) : (a \/ b) = (term127 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1484886 (_24816 : real) (_24817 : real) (_24818 : real) (_24819 : real) : (term150 _24816 _24818 _24817 _24819) = (term153 _24816 _24817 _24818 _24819).
Proof. exact (@lem1484885 (term154 _24816 _24818 _24817 _24819) ((real_add _24816 _24817) = (real_add _24818 _24819))). Qed.
Lemma lem1484888 (a : Prop) (b : Prop) : (term130 a b) = (term131 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1484889 (_24816 : real) (_24818 : real) (_24817 : real) (_24819 : real) : (term155 _24816 _24818 _24817 _24819) = (term156 _24816 _24818 _24817 _24819).
Proof. exact (@lem1484888 (term120 _24816 _24818) (term120 _24817 _24819)). Qed.
Lemma lem1484891 (a : Prop) : (term134 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1484892 (_24816 : real) (_24818 : real) : (term135 _24816 _24818) = (_24816 = _24818).
Proof. exact (@lem1484891 (_24816 = _24818)). Qed.
Lemma lem1484893 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1484894 (_24816 : real) (_24818 : real) : (term136 _24816 _24818) = (term137 _24816 _24818).
Proof. exact (MK_COMB (@lem1484893) (@lem1484892 _24816 _24818)). Qed.
Lemma lem1484896 (a : Prop) : (term134 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1484897 (_24817 : real) (_24819 : real) : (term135 _24817 _24819) = (_24817 = _24819).
Proof. exact (@lem1484896 (_24817 = _24819)). Qed.
Lemma lem1484898 (_24816 : real) (_24818 : real) (_24817 : real) (_24819 : real) : (term156 _24816 _24818 _24817 _24819) = (term157 _24816 _24818 _24817 _24819).
Proof. exact (MK_COMB (@lem1484894 _24816 _24818) (@lem1484897 _24817 _24819)). Qed.
Lemma lem1484899 (_24816 : real) (_24818 : real) (_24817 : real) (_24819 : real) : (term155 _24816 _24818 _24817 _24819) = (term157 _24816 _24818 _24817 _24819).
Proof. exact (TRANS (@lem1484889 _24816 _24818 _24817 _24819) (@lem1484898 _24816 _24818 _24817 _24819)). Qed.
Lemma lem1484900 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1484901 (_24816 : real) (_24818 : real) (_24817 : real) (_24819 : real) : (term158 _24816 _24818 _24817 _24819) = (term159 _24816 _24818 _24817 _24819).
Proof. exact (MK_COMB (@lem1484900) (@lem1484899 _24816 _24818 _24817 _24819)). Qed.
Lemma lem1484902 (_24816 : real) (_24817 : real) (_24818 : real) (_24819 : real) : ((real_add _24816 _24817) = (real_add _24818 _24819)) = ((real_add _24816 _24817) = (real_add _24818 _24819)).
Proof. exact (eq_refl ((real_add _24816 _24817) = (real_add _24818 _24819))). Qed.
Lemma lem1484903 (_24816 : real) (_24817 : real) (_24818 : real) (_24819 : real) : (term153 _24816 _24817 _24818 _24819) = (term160 _24816 _24817 _24818 _24819).
Proof. exact (MK_COMB (@lem1484901 _24816 _24818 _24817 _24819) (@lem1484902 _24816 _24817 _24818 _24819)). Qed.
Lemma lem1484904 (_24816 : real) (_24817 : real) (_24818 : real) (_24819 : real) : (term150 _24816 _24818 _24817 _24819) = (term160 _24816 _24817 _24818 _24819).
Proof. exact (TRANS (@lem1484886 _24816 _24817 _24818 _24819) (@lem1484903 _24816 _24817 _24818 _24819)). Qed.
Lemma lem1484906 (m : nat) (d : nat) (h1 : term96) (h2 : term74) : term161 m d.
Proof. exact (conj (@lem1484785 m h1 h2) (@lem1484793 d)). Qed.
Lemma lem1484908 (_24816 : real) (_24817 : real) (_24818 : real) (_24819 : real) : term160 _24816 _24817 _24818 _24819.
Proof. exact (EQ_MP (@lem1484904 _24816 _24817 _24818 _24819) (@lem1484883 _24816 _24818 _24817 _24819)). Qed.
Lemma lem1484909 (m : nat) (d : nat) : term162 m d.
Proof. exact (@lem1484908 term92 (real_of_num d) (term109 m) (real_of_num d)). Qed.
Lemma lem1484912 (m : nat) (d : nat) (h1 : term96) (h2 : term74) : (term163 d) = (term108 m d).
Proof. exact (@lem1484909 m d (@lem1484906 m d h1 h2)). Qed.
Lemma lem1484913 (m : nat) (d : nat) (h1 : term96) (h2 : term74) : term164 m d.
Proof. exact (fun h0 : term165 m d => @lem1484912 m d h1 h2). Qed.
Lemma lem1484915 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1484916 (m : nat) (d : nat) : (term164 m d) = ((term163 d) = (term108 m d)).
Proof. exact (@lem1484915 ((term163 d) = (term108 m d))). Qed.
Lemma lem1484917 (m : nat) (d : nat) (h1 : term96) (h2 : term74) : (term163 d) = (term108 m d).
Proof. exact (EQ_MP (@lem1484916 m d) (@lem1484913 m d h1 h2)). Qed.
Lemma lem1484919 (_24808 : real) (h1 : term99) : (term97 _24808) = _24808.
Proof. exact (EQ_MP (@lem1484576 _24808) (@lem1484575 _24808 h1)). Qed.
Lemma lem1484920 (d : nat) (h1 : term99) : (term163 d) = (real_of_num d).
Proof. exact (@lem1484919 (real_of_num d) h1). Qed.
Lemma lem1484921 (d : nat) (h1 : term99) : term166 d.
Proof. exact (fun h0 : term167 d => @lem1484920 d h1). Qed.
Lemma lem1484923 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1484924 (d : nat) : (term166 d) = ((term163 d) = (real_of_num d)).
Proof. exact (@lem1484923 ((term163 d) = (real_of_num d))). Qed.
Lemma lem1484925 (d : nat) (h1 : term99) : (term163 d) = (real_of_num d).
Proof. exact (EQ_MP (@lem1484924 d) (@lem1484921 d h1)). Qed.
Lemma lem1484926 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) : term168 m d.
Proof. exact (conj (@lem1484917 m d h1 h2) (@lem1484925 d h3)). Qed.
Lemma lem1484928 (x : real) (y : real) (z : real) : term141 x y z.
Proof. exact (EQ_MP (@lem1484772 x y z) (@lem1484751 y x z)). Qed.
Lemma lem1484929 (m : nat) (d : nat) : term169 m d.
Proof. exact (@lem1484928 (term163 d) (term108 m d) (real_of_num d)). Qed.
Lemma lem1484932 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) : (term108 m d) = (real_of_num d).
Proof. exact (@lem1484929 m d (@lem1484926 m d h1 h2 h3)). Qed.
Lemma lem1484933 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) : term170 m d.
Proof. exact (fun h0 : term171 m d => @lem1484932 m d h1 h2 h3). Qed.
Lemma lem1484935 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1484936 (m : nat) (d : nat) : (term170 m d) = ((term108 m d) = (real_of_num d)).
Proof. exact (@lem1484935 ((term108 m d) = (real_of_num d))). Qed.
Lemma lem1484937 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) : (term108 m d) = (real_of_num d).
Proof. exact (EQ_MP (@lem1484936 m d) (@lem1484933 m d h1 h2 h3)). Qed.
Lemma lem1484938 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) : term172 m d.
Proof. exact (conj (@lem1484645 d m h1) (@lem1484937 m d h1 h2 h3)). Qed.
Lemma lem1484940 (x : real) (y : real) (z : real) : term141 x y z.
Proof. exact (EQ_MP (@lem1484772 x y z) (@lem1484751 y x z)). Qed.
Lemma lem1484941 (m : nat) (d : nat) : term173 m d.
Proof. exact (@lem1484940 (term108 m d) (term62 d m) (real_of_num d)). Qed.
Lemma lem1484944 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) : (term62 d m) = (real_of_num d).
Proof. exact (@lem1484941 m d (@lem1484938 m d h1 h2 h3)). Qed.
Lemma lem1484945 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) : term174 m d.
Proof. exact (fun h0 : term67 m d => @lem1484944 m d h1 h2 h3). Qed.
Lemma lem1484947 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1484948 (m : nat) (d : nat) : (term174 m d) = ((term62 d m) = (real_of_num d)).
Proof. exact (@lem1484947 ((term62 d m) = (real_of_num d))). Qed.
Lemma lem1484949 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) : (term62 d m) = (real_of_num d).
Proof. exact (EQ_MP (@lem1484948 m d) (@lem1484945 m d h1 h2 h3)). Qed.
Lemma lem1484952 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1484954 (m : nat) (d : nat) : (term67 m d) = (term175 m d).
Proof. exact (@lem1484952 ((term62 d m) = (real_of_num d))). Qed.
Lemma lem1484957 (m : nat) (d : nat) (h1 : term67 m d) : term175 m d.
Proof. exact (EQ_MP (@lem1484954 m d) (@lem1484588 m d h1)). Qed.
Lemma lem1484960 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : False.
Proof. exact (@lem1484957 m d h4 (@lem1484949 m d h1 h2 h3)). Qed.
Lemma lem1484961 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : term176.
Proof. exact (fun h0 : ~ False => @lem1484960 m d h1 h2 h3 h4). Qed.
Lemma lem1484963 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1484964 : term176 = False.
Proof. exact (@lem1484963 False). Qed.
Lemma lem1484965 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : False.
Proof. exact (EQ_MP (@lem1484964) (@lem1484961 m d h1 h2 h3 h4)). Qed.
Lemma lem1484966 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : (term67 m d) = False.
Proof. exact (prop_ext (fun h5 : term67 m d => @lem1484965 m d h1 h2 h3 h4) (fun h5 : False => @lem1484588 m d h4)). Qed.
Lemma lem1484967 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : False.
Proof. exact (EQ_MP (@lem1484966 m d h1 h2 h3 h4) (@lem1484588 m d h4)). Qed.
Lemma lem1484968 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : (term67 m d) = False.
Proof. exact (prop_ext (fun h5 : term67 m d => @lem1484967 m d h1 h2 h3 h4) (fun h5 : False => @lem1484550 m d h4)). Qed.
Lemma lem1484969 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : False.
Proof. exact (EQ_MP (@lem1484968 m d h1 h2 h3 h4) (@lem1484550 m d h4)). Qed.
Lemma lem1484970 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : term74 = False.
Proof. exact (prop_ext (fun h5 : term74 => @lem1484969 m d h1 h2 h3 h4) (fun h5 : False => @lem1484574 h2)). Qed.
Lemma lem1484971 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : False.
Proof. exact (EQ_MP (@lem1484970 m d h1 h2 h3 h4) (@lem1484574 h2)). Qed.
Lemma lem1484972 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : term96 = False.
Proof. exact (prop_ext (fun h5 : term96 => @lem1484971 m d h1 h2 h3 h4) (fun h5 : False => @lem1484567 h1)). Qed.
Lemma lem1484973 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : False.
Proof. exact (EQ_MP (@lem1484972 m d h1 h2 h3 h4) (@lem1484567 h1)). Qed.
Lemma lem1484974 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : term99 = False.
Proof. exact (prop_ext (fun h5 : term99 => @lem1484973 m d h1 h2 h3 h4) (fun h5 : False => @lem1484557 h3)). Qed.
Lemma lem1484975 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : False.
Proof. exact (EQ_MP (@lem1484974 m d h1 h2 h3 h4) (@lem1484557 h3)). Qed.
Lemma lem1484976 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : (term67 m d) = False.
Proof. exact (prop_ext (fun h5 : term67 m d => @lem1484975 m d h1 h2 h3 h4) (fun h5 : False => @lem1484550 m d h4)). Qed.
Lemma lem1484977 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : False.
Proof. exact (EQ_MP (@lem1484976 m d h1 h2 h3 h4) (@lem1484550 m d h4)). Qed.
Lemma lem1484978 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : term74 = False.
Proof. exact (prop_ext (fun h5 : term74 => @lem1484977 m d h1 h2 h3 h4) (fun h5 : False => @lem1484546 h2)). Qed.
Lemma lem1484979 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : False.
Proof. exact (EQ_MP (@lem1484978 m d h1 h2 h3 h4) (@lem1484546 h2)). Qed.
Lemma lem1484980 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : term96 = False.
Proof. exact (prop_ext (fun h5 : term96 => @lem1484979 m d h1 h2 h3 h4) (fun h5 : False => @lem1484527 h1)). Qed.
Lemma lem1484981 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : False.
Proof. exact (EQ_MP (@lem1484980 m d h1 h2 h3 h4) (@lem1484527 h1)). Qed.
Lemma lem1484982 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : term99 = False.
Proof. exact (prop_ext (fun h5 : term99 => @lem1484981 m d h1 h2 h3 h4) (fun h5 : False => @lem1484507 h3)). Qed.
Lemma lem1484983 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : False.
Proof. exact (EQ_MP (@lem1484982 m d h1 h2 h3 h4) (@lem1484507 h3)). Qed.
Lemma lem1484984 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : (term67 m d) = False.
Proof. exact (prop_ext (fun h5 : term67 m d => @lem1484983 m d h1 h2 h3 h4) (fun h5 : False => @lem1484490 m d h4)). Qed.
Lemma lem1484985 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : False.
Proof. exact (EQ_MP (@lem1484984 m d h1 h2 h3 h4) (@lem1484490 m d h4)). Qed.
Lemma lem1484986 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : term74 = False.
Proof. exact (prop_ext (fun h5 : term74 => @lem1484985 m d h1 h2 h3 h4) (fun h5 : False => @lem1484464 h2)). Qed.
Lemma lem1484987 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : False.
Proof. exact (EQ_MP (@lem1484986 m d h1 h2 h3 h4) (@lem1484464 h2)). Qed.
Lemma lem1484988 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : term96 = False.
Proof. exact (prop_ext (fun h5 : term96 => @lem1484987 m d h1 h2 h3 h4) (fun h5 : False => @lem1484451 h1)). Qed.
Lemma lem1484989 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : False.
Proof. exact (EQ_MP (@lem1484988 m d h1 h2 h3 h4) (@lem1484451 h1)). Qed.
Lemma lem1484990 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : term99 = False.
Proof. exact (prop_ext (fun h5 : term99 => @lem1484989 m d h1 h2 h3 h4) (fun h5 : False => @lem1484431 h3)). Qed.
Lemma lem1484991 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : False.
Proof. exact (EQ_MP (@lem1484990 m d h1 h2 h3 h4) (@lem1484431 h3)). Qed.
Lemma lem1484992 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : (term67 m d) = False.
Proof. exact (prop_ext (fun h5 : term67 m d => @lem1484991 m d h1 h2 h3 h4) (fun h5 : False => @lem1484418 m d h4)). Qed.
Lemma lem1484993 (m : nat) (d : nat) (h1 : term96) (h2 : term74) (h3 : term99) (h4 : term67 m d) : False.
Proof. exact (EQ_MP (@lem1484992 m d h1 h2 h3 h4) (@lem1484418 m d h4)). Qed.
Lemma lem1484994 (m : nat) (d : nat) (h1 : term96) (h2 : term99) (h3 : term67 m d) : term72.
Proof. exact (fun h0 : term74 => @lem1484993 m d h1 h0 h2 h3). Qed.
Lemma lem1484995 : term72 = term73.
Proof. exact (@lem69 term74). Qed.
Lemma lem1484996 (m : nat) (d : nat) (h1 : term96) (h2 : term99) (h3 : term67 m d) : term73.
Proof. exact (EQ_MP (@lem1484995) (@lem1484994 m d h1 h2 h3)). Qed.
Lemma lem1484997 (m : nat) (d : nat) (h1 : term99) (h2 : term67 m d) : term77.
Proof. exact (fun h0 : term96 => @lem1484996 m d h0 h1 h2). Qed.
Lemma lem1484998 (m : nat) (d : nat) (h1 : term67 m d) : term80.
Proof. exact (fun h0 : term99 => @lem1484997 m d h0 h1). Qed.
Lemma lem1484999 (m : nat) (d : nat) : term82 m d.
Proof. exact (fun h0 : term67 m d => @lem1484998 m d h0). Qed.
Lemma lem1485004 (d : nat) : term86 d.
Proof. exact (fun m : nat => @lem1484999 m d). Qed.
Lemma lem1485009 : term90.
Proof. exact (fun d : nat => @lem1485004 d). Qed.
Lemma lem1485010 : term89.
Proof. exact (EQ_MP (@lem1484408) (@lem1485009)). Qed.
Lemma lem1485011 (d : nat) : term177 d.
Proof. exact (@lem1485010 d). Qed.
Lemma lem1485012 (d : nat) : (term177 d) = (term85 d).
Proof. exact (eq_refl (term177 d)). Qed.
Lemma lem1485013 (d : nat) : term85 d.
Proof. exact (EQ_MP (@lem1485012 d) (@lem1485011 d)). Qed.
Lemma lem1485014 (d : nat) (m : nat) : term178 d m.
Proof. exact (@lem1485013 d m). Qed.
Lemma lem1485015 (m : nat) (d : nat) : (term178 d m) = (term68 m d).
Proof. exact (eq_refl (term178 d m)). Qed.
Lemma lem1485016 (m : nat) (d : nat) : term68 m d.
Proof. exact (EQ_MP (@lem1485015 m d) (@lem1485014 d m)). Qed.
Lemma lem1485018 (m : nat) (d : nat) : term68 m d.
Proof. exact (@lem1484264 m d (@lem1485016 m d)). Qed.
Lemma lem1485019 (m : nat) (d : nat) (h1 : term67 m d) : term79.
Proof. exact (@lem1485018 m d (@lem1484249 m d h1)). Qed.
Lemma lem1485020 (m : nat) (d : nat) (h1 : term67 m d) : term76.
Proof. exact (@lem1485019 m d h1 (@lem1338512)). Qed.
Lemma lem1485021 (m : nat) (d : nat) (h1 : term67 m d) : term72.
Proof. exact (@lem1485020 m d h1 (@lem1338238)). Qed.
Lemma lem1485022 (m : nat) (d : nat) (h1 : term67 m d) : False.
Proof. exact (@lem1485021 m d h1 (@lem1338588)). Qed.
Lemma lem1485023 (m : nat) (d : nat) (h1 : term67 m d) : (term67 m d) = False.
Proof. exact (prop_ext (fun h2 : term67 m d => @lem1485022 m d h1) (fun h2 : False => @lem1484249 m d h1)). Qed.
Lemma lem1485024 (m : nat) (d : nat) (h1 : term67 m d) : False.
Proof. exact (EQ_MP (@lem1485023 m d h1) (@lem1484249 m d h1)). Qed.
Lemma lem1485025 (m : nat) (d : nat) : term66 m d.
Proof. exact (fun h0 : term67 m d => @lem1485024 m d h0). Qed.
Lemma lem1485026 (m : nat) (d : nat) : (term62 d m) = (real_of_num d).
Proof. exact (EQ_MP (@lem1484248 m d) (@lem1485025 m d)). Qed.
Lemma lem1485027 (m : nat) (d : nat) : (term59 d m) = (real_of_num d).
Proof. exact (EQ_MP (@lem1484244 m d) (@lem1485026 m d)). Qed.
Lemma lem1485028 (m : nat) (d : nat) : (term57 d m) = (real_of_num d).
Proof. exact (EQ_MP (@lem1484228 m d) (@lem1485027 m d)). Qed.
Lemma lem1485029 (m : nat) (d : nat) : (term52 d m) = (real_of_num d).
Proof. exact (EQ_MP (@lem1484214 m d) (@lem1485028 m d)). Qed.
Lemma lem1485030 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term42 n m) = (term43 n m).
Proof. exact (EQ_MP (@lem1484198 n m d h1) (@lem1485029 m d)). Qed.
Lemma lem1485031 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (n = (Nat.add m d)) = ((term42 n m) = (term43 n m)).
Proof. exact (prop_ext (fun h2 : n = (Nat.add m d) => @lem1485030 n m d h1) (fun h2 : (term42 n m) = (term43 n m) => @lem1484164 n m d h1)). Qed.
Lemma lem1485032 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term42 n m) = (term43 n m).
Proof. exact (EQ_MP (@lem1485031 n m d h1) (@lem1484164 n m d h1)). Qed.
Lemma lem1485033 (n : nat) (m : nat) (h1 : term39 n m) : (term42 n m) = (term43 n m).
Proof. exact (ex_elim (@lem1484163 n m h1) (fun d : nat => fun h0 : term179 n m d => @lem1485032 n m d h0)). Qed.
Lemma lem1485034 (n : nat) (m : nat) : term45 n m.
Proof. exact (fun h0 : term39 n m => @lem1485033 n m h0). Qed.
Lemma lem1485035 (n : nat) (m : nat) : term44 n m.
Proof. exact (EQ_MP (@lem1484162 n m) (@lem1485034 n m)). Qed.
Lemma lem1485040 (m : nat) : term180 m.
Proof. exact (fun n : nat => @lem1485035 n m). Qed.
Lemma lem1485045 : term181.
Proof. exact (fun m : nat => @lem1485040 m). Qed.
