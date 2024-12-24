Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1320203_term_abbrevs.
Require Import NADD_ADD_ASSOC_spec.
Require Import thm1317906_spec.
Require Import thm1317911_spec.
Require Import thm1318759_spec.
Require Import thm1318760_spec.
Require Import thm1318766_spec.
Require Import thm1318767_spec.
Lemma lem1320063 (x : nadd) (y : nadd) : (nadd_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1318767 x y) (@lem1318766 x y)). Qed.
Lemma lem1320064 (x : nadd) (y : nadd) (z : nadd) : (term1 x y z) = ((term2 x y z) = (term3 x y z)).
Proof. exact (@lem1320063 (term4 x y z) (term5 x y z)). Qed.
Lemma lem1320068 (x : nadd) (y : nadd) : (term6 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem1317911 x y) (@lem1317906 x y)). Qed.
Lemma lem1320069 (x : nadd) (y : nadd) (z : nadd) : (term2 x y z) = (term8 x y z).
Proof. exact (@lem1320068 x (nadd_add y z)). Qed.
Lemma lem1320071 (x : nadd) (y : nadd) : (term6 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem1317911 x y) (@lem1317906 x y)). Qed.
Lemma lem1320072 (y : nadd) (z : nadd) : (term6 y z) = (term7 y z).
Proof. exact (@lem1320071 y z). Qed.
Lemma lem1320073 (x : nadd) : (term9 x) = (term9 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1320074 (x : nadd) (y : nadd) (z : nadd) : (term8 x y z) = (term10 x y z).
Proof. exact (MK_COMB (@lem1320073 x) (@lem1320072 y z)). Qed.
Lemma lem1320075 (x : nadd) (y : nadd) (z : nadd) : (term2 x y z) = (term10 x y z).
Proof. exact (TRANS (@lem1320069 x y z) (@lem1320074 x y z)). Qed.
Lemma lem1320076 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1320077 (x : nadd) (y : nadd) (z : nadd) : (term11 x y z) = (term12 x y z).
Proof. exact (MK_COMB (@lem1320076) (@lem1320075 x y z)). Qed.
Lemma lem1320079 (x : nadd) (y : nadd) : (term6 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem1317911 x y) (@lem1317906 x y)). Qed.
Lemma lem1320080 (x : nadd) (y : nadd) (z : nadd) : (term3 x y z) = (term13 x y z).
Proof. exact (@lem1320079 (nadd_add x y) z). Qed.
Lemma lem1320082 (x : nadd) (y : nadd) : (term6 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem1317911 x y) (@lem1317906 x y)). Qed.
Lemma lem1320083 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1320084 (x : nadd) (y : nadd) : (term14 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem1320083) (@lem1320082 x y)). Qed.
Lemma lem1320085 (z : nadd) : (term0 z) = (term0 z).
Proof. exact (eq_refl (term0 z)). Qed.
Lemma lem1320086 (x : nadd) (y : nadd) (z : nadd) : (term13 x y z) = (term16 x y z).
Proof. exact (MK_COMB (@lem1320084 x y) (@lem1320085 z)). Qed.
Lemma lem1320087 (x : nadd) (y : nadd) (z : nadd) : (term3 x y z) = (term16 x y z).
Proof. exact (TRANS (@lem1320080 x y z) (@lem1320086 x y z)). Qed.
Lemma lem1320088 (x : nadd) (y : nadd) (z : nadd) : ((term2 x y z) = (term3 x y z)) = ((term10 x y z) = (term16 x y z)).
Proof. exact (MK_COMB (@lem1320077 x y z) (@lem1320087 x y z)). Qed.
Lemma lem1320091 (x : nadd) (y : nadd) (z : nadd) : (term1 x y z) = ((term10 x y z) = (term16 x y z)).
Proof. exact (TRANS (@lem1320064 x y z) (@lem1320088 x y z)). Qed.
Lemma lem1320092 (x : nadd) (y : nadd) : (term17 x y) = (term18 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1320091 x y z)). Qed.
Lemma lem1320093 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320094 (x : nadd) (y : nadd) : (term19 x y) = (term20 x y).
Proof. exact (MK_COMB (@lem1320093) (@lem1320092 x y)). Qed.
Lemma lem1320100 (P : hreal -> Prop) : (term21 P) = (term22 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1320101 (x : nadd) (y : nadd) : (term23 x y) = (term24 x y).
Proof. exact (@lem1320100 (term25 x y)). Qed.
Lemma lem1320102 (x : nadd) (y : nadd) (z : nadd) : (term26 x y z) = ((term10 x y z) = (term16 x y z)).
Proof. exact (eq_refl (term26 x y z)). Qed.
Lemma lem1320103 (x : nadd) (y : nadd) : (term27 x y) = (term18 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1320102 x y z)). Qed.
Lemma lem1320104 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320105 (x : nadd) (y : nadd) : (term23 x y) = (term20 x y).
Proof. exact (MK_COMB (@lem1320104) (@lem1320103 x y)). Qed.
Lemma lem1320106 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1320107 (x : nadd) (y : nadd) : (term28 x y) = (term29 x y).
Proof. exact (MK_COMB (@lem1320106) (@lem1320105 x y)). Qed.
Lemma lem1320108 (x : nadd) (y : nadd) (z : hreal) : (term30 x y z) = ((term31 x y z) = (term32 x y z)).
Proof. exact (eq_refl (term30 x y z)). Qed.
Lemma lem1320109 (x : nadd) (y : nadd) : (term33 x y) = (term25 x y).
Proof. exact (fun_ext (fun z : hreal => @lem1320108 x y z)). Qed.
Lemma lem1320110 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1320111 (x : nadd) (y : nadd) : (term24 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem1320110) (@lem1320109 x y)). Qed.
Lemma lem1320112 (x : nadd) (y : nadd) : ((term23 x y) = (term24 x y)) = ((term20 x y) = (term34 x y)).
Proof. exact (MK_COMB (@lem1320107 x y) (@lem1320111 x y)). Qed.
Lemma lem1320113 (x : nadd) (y : nadd) : (term20 x y) = (term34 x y).
Proof. exact (EQ_MP (@lem1320112 x y) (@lem1320101 x y)). Qed.
Lemma lem1320122 (x : nadd) (y : nadd) : (term19 x y) = (term34 x y).
Proof. exact (TRANS (@lem1320094 x y) (@lem1320113 x y)). Qed.
Lemma lem1320123 (x : nadd) : (term35 x) = (term36 x).
Proof. exact (fun_ext (fun y : nadd => @lem1320122 x y)). Qed.
Lemma lem1320124 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320125 (x : nadd) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem1320124) (@lem1320123 x)). Qed.
Lemma lem1320131 (P : hreal -> Prop) : (term21 P) = (term22 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1320132 (x : nadd) : (term39 x) = (term40 x).
Proof. exact (@lem1320131 (term41 x)). Qed.
Lemma lem1320133 (x : nadd) (y : nadd) : (term42 x y) = (term34 x y).
Proof. exact (eq_refl (term42 x y)). Qed.
Lemma lem1320134 (x : nadd) : (term43 x) = (term36 x).
Proof. exact (fun_ext (fun y : nadd => @lem1320133 x y)). Qed.
Lemma lem1320135 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320136 (x : nadd) : (term39 x) = (term38 x).
Proof. exact (MK_COMB (@lem1320135) (@lem1320134 x)). Qed.
Lemma lem1320137 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1320138 (x : nadd) : (term44 x) = (term45 x).
Proof. exact (MK_COMB (@lem1320137) (@lem1320136 x)). Qed.
Lemma lem1320139 (x : nadd) (y : hreal) : (term46 x y) = (term47 x y).
Proof. exact (eq_refl (term46 x y)). Qed.
Lemma lem1320140 (x : nadd) : (term48 x) = (term41 x).
Proof. exact (fun_ext (fun y : hreal => @lem1320139 x y)). Qed.
Lemma lem1320141 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1320142 (x : nadd) : (term40 x) = (term49 x).
Proof. exact (MK_COMB (@lem1320141) (@lem1320140 x)). Qed.
Lemma lem1320143 (x : nadd) : ((term39 x) = (term40 x)) = ((term38 x) = (term49 x)).
Proof. exact (MK_COMB (@lem1320138 x) (@lem1320142 x)). Qed.
Lemma lem1320144 (x : nadd) : (term38 x) = (term49 x).
Proof. exact (EQ_MP (@lem1320143 x) (@lem1320132 x)). Qed.
Lemma lem1320159 (x : nadd) : (term37 x) = (term49 x).
Proof. exact (TRANS (@lem1320125 x) (@lem1320144 x)). Qed.
Lemma lem1320160 : term50 = term51.
Proof. exact (fun_ext (fun x : nadd => @lem1320159 x)). Qed.
Lemma lem1320161 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320162 : term52 = term53.
Proof. exact (MK_COMB (@lem1320161) (@lem1320160)). Qed.
Lemma lem1320168 (P : hreal -> Prop) : (term21 P) = (term22 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1320169 : term54 = term55.
Proof. exact (@lem1320168 term56). Qed.
Lemma lem1320170 (x : nadd) : (term57 x) = (term49 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem1320171 : term58 = term51.
Proof. exact (fun_ext (fun x : nadd => @lem1320170 x)). Qed.
Lemma lem1320172 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320173 : term54 = term53.
Proof. exact (MK_COMB (@lem1320172) (@lem1320171)). Qed.
Lemma lem1320174 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1320175 : term59 = term60.
Proof. exact (MK_COMB (@lem1320174) (@lem1320173)). Qed.
Lemma lem1320176 (x : hreal) : (term61 x) = (term62 x).
Proof. exact (eq_refl (term61 x)). Qed.
Lemma lem1320177 : term63 = term56.
Proof. exact (fun_ext (fun x : hreal => @lem1320176 x)). Qed.
Lemma lem1320178 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1320179 : term55 = term64.
Proof. exact (MK_COMB (@lem1320178) (@lem1320177)). Qed.
Lemma lem1320180 : (term54 = term55) = (term53 = term64).
Proof. exact (MK_COMB (@lem1320175) (@lem1320179)). Qed.
Lemma lem1320181 : term53 = term64.
Proof. exact (EQ_MP (@lem1320180) (@lem1320169)). Qed.
Lemma lem1320202 : term52 = term64.
Proof. exact (TRANS (@lem1320162) (@lem1320181)). Qed.
Lemma lem1320203 : term64.
Proof. exact (EQ_MP (@lem1320202) (@lem1274592)). Qed.
