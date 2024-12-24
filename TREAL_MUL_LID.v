Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_MUL_LID_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import HREAL_ADD_RID_spec.
Require Import HREAL_MUL_LZERO_spec.
Require Import thm0_spec.
Require Import thm1320890_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import treal_eq_spec.
Require Import treal_mul_spec.
Require Import treal_of_num_spec.
Lemma lem1329093 (n : hreal) : term0 n.
Proof. exact (@lem1321694 n). Qed.
Lemma lem1329094 (n : hreal) : (term0 n) = ((term1 n) = n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1329099 (x : hreal) : term2 x.
Proof. exact (@lem1320890 x). Qed.
Lemma lem1329100 (x : hreal) : (term2 x) = ((term3 x) = x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1329102 (m : hreal) : term4 m.
Proof. exact (@lem1321875 m). Qed.
Lemma lem1329103 (m : hreal) : (term4 m) = ((term5 m) = term6).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem1329105 (x1 : hreal) : term7 x1.
Proof. exact (@lem1326116 x1). Qed.
Lemma lem1329106 (x1 : hreal) : (term7 x1) = (term8 x1).
Proof. exact (eq_refl (term7 x1)). Qed.
Lemma lem1329107 (x1 : hreal) : term8 x1.
Proof. exact (EQ_MP (@lem1329106 x1) (@lem1329105 x1)). Qed.
Lemma lem1329108 (x1 : hreal) (y2 : hreal) : term9 x1 y2.
Proof. exact (@lem1329107 x1 y2). Qed.
Lemma lem1329109 (x1 : hreal) (y2 : hreal) : (term9 x1 y2) = (term10 x1 y2).
Proof. exact (eq_refl (term9 x1 y2)). Qed.
Lemma lem1329110 (x1 : hreal) (y2 : hreal) : term10 x1 y2.
Proof. exact (EQ_MP (@lem1329109 x1 y2) (@lem1329108 x1 y2)). Qed.
Lemma lem1329111 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term11 x1 y2 x2.
Proof. exact (@lem1329110 x1 y2 x2). Qed.
Lemma lem1329112 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term11 x1 y2 x2) = (term12 x1 y2 x2).
Proof. exact (eq_refl (term11 x1 y2 x2)). Qed.
Lemma lem1329113 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term12 x1 y2 x2.
Proof. exact (EQ_MP (@lem1329112 x1 y2 x2) (@lem1329111 x1 y2 x2)). Qed.
Lemma lem1329114 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term13 x1 y2 x2 y1.
Proof. exact (@lem1329113 x1 y2 x2 y1). Qed.
Lemma lem1329115 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term13 x1 y2 x2 y1) = ((term14 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1))).
Proof. exact (eq_refl (term13 x1 y2 x2 y1)). Qed.
Lemma lem1329117 (x1 : hreal) : term15 x1.
Proof. exact (@lem1324372 x1). Qed.
Lemma lem1329118 (x1 : hreal) : (term15 x1) = (term16 x1).
Proof. exact (eq_refl (term15 x1)). Qed.
Lemma lem1329119 (x1 : hreal) : term16 x1.
Proof. exact (EQ_MP (@lem1329118 x1) (@lem1329117 x1)). Qed.
Lemma lem1329120 (x1 : hreal) (y2 : hreal) : term17 x1 y2.
Proof. exact (@lem1329119 x1 y2). Qed.
Lemma lem1329121 (x1 : hreal) (y2 : hreal) : (term17 x1 y2) = (term18 x1 y2).
Proof. exact (eq_refl (term17 x1 y2)). Qed.
Lemma lem1329122 (x1 : hreal) (y2 : hreal) : term18 x1 y2.
Proof. exact (EQ_MP (@lem1329121 x1 y2) (@lem1329120 x1 y2)). Qed.
Lemma lem1329123 (x1 : hreal) (y2 : hreal) (y1 : hreal) : term19 x1 y2 y1.
Proof. exact (@lem1329122 x1 y2 y1). Qed.
Lemma lem1329124 (x1 : hreal) (y2 : hreal) (y1 : hreal) : (term19 x1 y2 y1) = (term20 x1 y2 y1).
Proof. exact (eq_refl (term19 x1 y2 y1)). Qed.
Lemma lem1329125 (x1 : hreal) (y2 : hreal) (y1 : hreal) : term20 x1 y2 y1.
Proof. exact (EQ_MP (@lem1329124 x1 y2 y1) (@lem1329123 x1 y2 y1)). Qed.
Lemma lem1329126 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : term21 x1 y2 y1 x2.
Proof. exact (@lem1329125 x1 y2 y1 x2). Qed.
Lemma lem1329127 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term21 x1 y2 y1 x2) = ((term22 x1 y1 x2 y2) = (term23 x1 y2 y1 x2)).
Proof. exact (eq_refl (term21 x1 y2 y1 x2)). Qed.
Lemma lem1329129 (n : nat) : term24 n.
Proof. exact (@lem1322742 n). Qed.
Lemma lem1329130 (n : nat) : (term24 n) = ((treal_of_num n) = (term25 n)).
Proof. exact (eq_refl (term24 n)). Qed.
Lemma lem1329132 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term26 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem1329133 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term26 _5106 _5107 P) = ((term27 _5106 _5107 P) = (term28 _5106 _5107 P)).
Proof. exact (eq_refl (term26 _5106 _5107 P)). Qed.
Lemma lem1329140 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term27 _5106 _5107 P) = (term28 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1329133 _5106 _5107 P) (@lem1329132 _5106 _5107 P)). Qed.
Lemma lem1329141 (P : type1233) : (term29 P) = (term30 P).
Proof. exact (@lem1329140 hreal hreal P). Qed.
Lemma lem1329142 : term31 = term32.
Proof. exact (@lem1329141 term33). Qed.
Lemma lem1329143 (x : prod hreal hreal) : (term34 x) = (term35 x).
Proof. exact (eq_refl (term34 x)). Qed.
Lemma lem1329144 : term36 = term33.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1329143 x)). Qed.
Lemma lem1329145 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1329146 : term31 = term37.
Proof. exact (MK_COMB (@lem1329145) (@lem1329144)). Qed.
Lemma lem1329147 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1329148 : term38 = term39.
Proof. exact (MK_COMB (@lem1329147) (@lem1329146)). Qed.
Lemma lem1329149 (p1 : hreal) (p2 : hreal) : (term40 p1 p2) = (term41 p1 p2).
Proof. exact (eq_refl (term40 p1 p2)). Qed.
Lemma lem1329150 (p1 : hreal) : (term42 p1) = (term43 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1329149 p1 p2)). Qed.
Lemma lem1329151 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329152 (p1 : hreal) : (term44 p1) = (term45 p1).
Proof. exact (MK_COMB (@lem1329151) (@lem1329150 p1)). Qed.
Lemma lem1329153 : term46 = term47.
Proof. exact (fun_ext (fun p1 : hreal => @lem1329152 p1)). Qed.
Lemma lem1329154 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329155 : term32 = term48.
Proof. exact (MK_COMB (@lem1329154) (@lem1329153)). Qed.
Lemma lem1329156 : (term31 = term32) = (term37 = term48).
Proof. exact (MK_COMB (@lem1329148) (@lem1329155)). Qed.
Lemma lem1329157 : term37 = term48.
Proof. exact (EQ_MP (@lem1329156) (@lem1329142)). Qed.
Lemma lem1329171 (n : nat) : (treal_of_num n) = (term25 n).
Proof. exact (EQ_MP (@lem1329130 n) (@lem1329129 n)). Qed.
Lemma lem1329172 : term49 = term50.
Proof. exact (@lem1329171 term51). Qed.
Lemma lem1329173 : treal_mul = treal_mul.
Proof. exact (eq_refl treal_mul). Qed.
Lemma lem1329174 : term52 = term53.
Proof. exact (MK_COMB (@lem1329173) (@lem1329172)). Qed.
Lemma lem1329175 (p1 : hreal) (p2 : hreal) : (@pair hreal hreal p1 p2) = (@pair hreal hreal p1 p2).
Proof. exact (eq_refl (@pair hreal hreal p1 p2)). Qed.
Lemma lem1329176 (p1 : hreal) (p2 : hreal) : (term54 p1 p2) = (term55 p1 p2).
Proof. exact (MK_COMB (@lem1329174) (@lem1329175 p1 p2)). Qed.
Lemma lem1329178 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term22 x1 y1 x2 y2) = (term23 x1 y2 y1 x2).
Proof. exact (EQ_MP (@lem1329127 x1 y2 y1 x2) (@lem1329126 x1 y2 y1 x2)). Qed.
Lemma lem1329179 (p2 : hreal) (p1 : hreal) : (term55 p1 p2) = (term56 p2 p1).
Proof. exact (@lem1329178 term57 p2 term6 p1). Qed.
Lemma lem1329180 (p2 : hreal) (p1 : hreal) : (term54 p1 p2) = (term56 p2 p1).
Proof. exact (TRANS (@lem1329176 p1 p2) (@lem1329179 p2 p1)). Qed.
Lemma lem1329181 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1329182 (p2 : hreal) (p1 : hreal) : (term58 p1 p2) = (term59 p2 p1).
Proof. exact (MK_COMB (@lem1329181) (@lem1329180 p2 p1)). Qed.
Lemma lem1329183 (p1 : hreal) (p2 : hreal) : (@pair hreal hreal p1 p2) = (@pair hreal hreal p1 p2).
Proof. exact (eq_refl (@pair hreal hreal p1 p2)). Qed.
Lemma lem1329184 (p1 : hreal) (p2 : hreal) : (term41 p1 p2) = (term60 p1 p2).
Proof. exact (MK_COMB (@lem1329182 p2 p1) (@lem1329183 p1 p2)). Qed.
Lemma lem1329186 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term14 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1329115 x1 y2 x2 y1) (@lem1329114 x1 y2 x2 y1)). Qed.
Lemma lem1329187 (p2 : hreal) (p1 : hreal) : (term60 p1 p2) = ((term61 p1 p2) = (term62 p2 p1)).
Proof. exact (@lem1329186 (term63 p1 p2) p2 p1 (term63 p2 p1)). Qed.
Lemma lem1329190 (p2 : hreal) (p1 : hreal) : (term41 p1 p2) = ((term61 p1 p2) = (term62 p2 p1)).
Proof. exact (TRANS (@lem1329184 p1 p2) (@lem1329187 p2 p1)). Qed.
Lemma lem1329191 (p1 : hreal) : (term43 p1) = (term64 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1329190 p2 p1)). Qed.
Lemma lem1329194 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329195 (p1 : hreal) : (term45 p1) = (term65 p1).
Proof. exact (MK_COMB (@lem1329194) (@lem1329191 p1)). Qed.
Lemma lem1329204 : term47 = term66.
Proof. exact (fun_ext (fun p1 : hreal => @lem1329195 p1)). Qed.
Lemma lem1329213 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329214 : term48 = term67.
Proof. exact (MK_COMB (@lem1329213) (@lem1329204)). Qed.
Lemma lem1329229 : term37 = term67.
Proof. exact (TRANS (@lem1329157) (@lem1329214)). Qed.
Lemma lem1329230 : term67 = term37.
Proof. exact (SYM (@lem1329229)). Qed.
Lemma lem1329242 (x : hreal) : (term3 x) = x.
Proof. exact (EQ_MP (@lem1329100 x) (@lem1329099 x)). Qed.
Lemma lem1329243 (p1 : hreal) : (term3 p1) = p1.
Proof. exact (@lem1329242 p1). Qed.
Lemma lem1329244 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1329245 (p1 : hreal) : (term68 p1) = (hreal_add p1).
Proof. exact (MK_COMB (@lem1329244) (@lem1329243 p1)). Qed.
Lemma lem1329247 (m : hreal) : (term5 m) = term6.
Proof. exact (EQ_MP (@lem1329103 m) (@lem1329102 m)). Qed.
Lemma lem1329248 (p2 : hreal) : (term5 p2) = term6.
Proof. exact (@lem1329247 p2). Qed.
Lemma lem1329249 (p2 : hreal) (p1 : hreal) : (term63 p1 p2) = (term1 p1).
Proof. exact (MK_COMB (@lem1329245 p1) (@lem1329248 p2)). Qed.
Lemma lem1329251 (n : hreal) : (term1 n) = n.
Proof. exact (EQ_MP (@lem1329094 n) (@lem1329093 n)). Qed.
Lemma lem1329252 (p1 : hreal) : (term1 p1) = p1.
Proof. exact (@lem1329251 p1). Qed.
Lemma lem1329253 (p2 : hreal) (p1 : hreal) : (term63 p1 p2) = p1.
Proof. exact (TRANS (@lem1329249 p2 p1) (@lem1329252 p1)). Qed.
Lemma lem1329254 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1329255 (p2 : hreal) (p1 : hreal) : (term69 p1 p2) = (hreal_add p1).
Proof. exact (MK_COMB (@lem1329254) (@lem1329253 p2 p1)). Qed.
Lemma lem1329256 (p2 : hreal) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem1329257 (p1 : hreal) (p2 : hreal) : (term61 p1 p2) = (hreal_add p1 p2).
Proof. exact (MK_COMB (@lem1329255 p2 p1) (@lem1329256 p2)). Qed.
Lemma lem1329258 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1329259 (p1 : hreal) (p2 : hreal) : (term70 p1 p2) = (term71 p1 p2).
Proof. exact (MK_COMB (@lem1329258) (@lem1329257 p1 p2)). Qed.
Lemma lem1329261 (x : hreal) : (term3 x) = x.
Proof. exact (EQ_MP (@lem1329100 x) (@lem1329099 x)). Qed.
Lemma lem1329262 (p2 : hreal) : (term3 p2) = p2.
Proof. exact (@lem1329261 p2). Qed.
Lemma lem1329263 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1329264 (p2 : hreal) : (term68 p2) = (hreal_add p2).
Proof. exact (MK_COMB (@lem1329263) (@lem1329262 p2)). Qed.
Lemma lem1329266 (m : hreal) : (term5 m) = term6.
Proof. exact (EQ_MP (@lem1329103 m) (@lem1329102 m)). Qed.
Lemma lem1329267 (p1 : hreal) : (term5 p1) = term6.
Proof. exact (@lem1329266 p1). Qed.
Lemma lem1329268 (p1 : hreal) (p2 : hreal) : (term63 p2 p1) = (term1 p2).
Proof. exact (MK_COMB (@lem1329264 p2) (@lem1329267 p1)). Qed.
Lemma lem1329270 (n : hreal) : (term1 n) = n.
Proof. exact (EQ_MP (@lem1329094 n) (@lem1329093 n)). Qed.
Lemma lem1329271 (p2 : hreal) : (term1 p2) = p2.
Proof. exact (@lem1329270 p2). Qed.
Lemma lem1329272 (p1 : hreal) (p2 : hreal) : (term63 p2 p1) = p2.
Proof. exact (TRANS (@lem1329268 p1 p2) (@lem1329271 p2)). Qed.
Lemma lem1329273 (p1 : hreal) : (hreal_add p1) = (hreal_add p1).
Proof. exact (eq_refl (hreal_add p1)). Qed.
Lemma lem1329274 (p1 : hreal) (p2 : hreal) : (term62 p2 p1) = (hreal_add p1 p2).
Proof. exact (MK_COMB (@lem1329273 p1) (@lem1329272 p1 p2)). Qed.
Lemma lem1329275 (p1 : hreal) (p2 : hreal) : ((term61 p1 p2) = (term62 p2 p1)) = ((hreal_add p1 p2) = (hreal_add p1 p2)).
Proof. exact (MK_COMB (@lem1329259 p1 p2) (@lem1329274 p1 p2)). Qed.
Lemma lem1329277 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1329278 (x : hreal) : (x = x) = True.
Proof. exact (@lem1329277 hreal x). Qed.
Lemma lem1329279 (p1 : hreal) (p2 : hreal) : ((hreal_add p1 p2) = (hreal_add p1 p2)) = True.
Proof. exact (@lem1329278 (hreal_add p1 p2)). Qed.
Lemma lem1329280 (p2 : hreal) (p1 : hreal) : ((term61 p1 p2) = (term62 p2 p1)) = True.
Proof. exact (TRANS (@lem1329275 p1 p2) (@lem1329279 p1 p2)). Qed.
Lemma lem1329281 (p1 : hreal) : (term64 p1) = term72.
Proof. exact (fun_ext (fun p2 : hreal => @lem1329280 p2 p1)). Qed.
Lemma lem1329282 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329283 (p1 : hreal) : (term65 p1) = term73.
Proof. exact (MK_COMB (@lem1329282) (@lem1329281 p1)). Qed.
Lemma lem1329285 {A : Type'} (t : Prop) : (term74 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1329286 (t : Prop) : (term75 t) = t.
Proof. exact (@lem1329285 hreal t). Qed.
Lemma lem1329287 : term73 = True.
Proof. exact (@lem1329286 True). Qed.
Lemma lem1329288 (p1 : hreal) : (term65 p1) = True.
Proof. exact (TRANS (@lem1329283 p1) (@lem1329287)). Qed.
Lemma lem1329289 : term66 = term72.
Proof. exact (fun_ext (fun p1 : hreal => @lem1329288 p1)). Qed.
Lemma lem1329290 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329291 : term67 = term73.
Proof. exact (MK_COMB (@lem1329290) (@lem1329289)). Qed.
Lemma lem1329293 {A : Type'} (t : Prop) : (term74 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1329294 (t : Prop) : (term75 t) = t.
Proof. exact (@lem1329293 hreal t). Qed.
Lemma lem1329295 : term73 = True.
Proof. exact (@lem1329294 True). Qed.
Lemma lem1329296 : term67 = True.
Proof. exact (TRANS (@lem1329291) (@lem1329295)). Qed.
Lemma lem1329297 : True = term67.
Proof. exact (SYM (@lem1329296)). Qed.
Lemma lem1329298 : term67.
Proof. exact (EQ_MP (@lem1329297) (@lem0)). Qed.
Lemma lem1329299 : term37.
Proof. exact (EQ_MP (@lem1329230) (@lem1329298)). Qed.
