Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LENGTH_ZIP_term_abbrevs.
Require Import NOT_SUC_spec.
Require Import SUC_INJ_spec.
Require Import ZIP_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097080_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm82_spec.
Lemma lem1156057 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1156058 {_27176 : Type'} (P : type1143 _27176) : term0 _27176 P.
Proof. exact (@lem1156057 _27176 P). Qed.
Lemma lem1156059 {_27176 _27178 : Type'} : term1 _27176 _27178.
Proof. exact (@lem1156058 _27176 (term2 _27176 _27178)). Qed.
Lemma lem1156060 {_27176 _27178 : Type'} : (term3 _27176 _27178) = (term4 _27176 _27178).
Proof. exact (eq_refl (term3 _27176 _27178)). Qed.
Lemma lem1156061 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1156062 {_27176 _27178 : Type'} : (term5 _27176 _27178) = (term6 _27176 _27178).
Proof. exact (MK_COMB (@lem1156061) (@lem1156060 _27176 _27178)). Qed.
Lemma lem1156063 {_27176 _27178 : Type'} (t : list _27176) : (term7 _27176 _27178 t) = (term8 _27176 _27178 t).
Proof. exact (eq_refl (term7 _27176 _27178 t)). Qed.
Lemma lem1156064 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1156065 {_27176 _27178 : Type'} (t : list _27176) : (term9 _27176 _27178 t) = (term10 _27176 _27178 t).
Proof. exact (MK_COMB (@lem1156064) (@lem1156063 _27176 _27178 t)). Qed.
Lemma lem1156066 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) : (term11 _27176 _27178 h t) = (term12 _27176 _27178 h t).
Proof. exact (eq_refl (term11 _27176 _27178 h t)). Qed.
Lemma lem1156067 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) : (term13 _27176 _27178 h t) = (term14 _27176 _27178 h t).
Proof. exact (MK_COMB (@lem1156065 _27176 _27178 t) (@lem1156066 _27176 _27178 h t)). Qed.
Lemma lem1156068 {_27176 _27178 : Type'} (h : _27176) : (term15 _27176 _27178 h) = (term16 _27176 _27178 h).
Proof. exact (fun_ext (fun t : list _27176 => @lem1156067 _27176 _27178 h t)). Qed.
Lemma lem1156069 {_27176 : Type'} : (@all (list _27176)) = (@all (list _27176)).
Proof. exact (eq_refl (@all (list _27176))). Qed.
Lemma lem1156070 {_27176 _27178 : Type'} (h : _27176) : (term17 _27176 _27178 h) = (term18 _27176 _27178 h).
Proof. exact (MK_COMB (@lem1156069 _27176) (@lem1156068 _27176 _27178 h)). Qed.
Lemma lem1156071 {_27176 _27178 : Type'} : (term19 _27176 _27178) = (term20 _27176 _27178).
Proof. exact (fun_ext (fun h : _27176 => @lem1156070 _27176 _27178 h)). Qed.
Lemma lem1156072 {_27176 : Type'} : (@all _27176) = (@all _27176).
Proof. exact (eq_refl (@all _27176)). Qed.
Lemma lem1156073 {_27176 _27178 : Type'} : (term21 _27176 _27178) = (term22 _27176 _27178).
Proof. exact (MK_COMB (@lem1156072 _27176) (@lem1156071 _27176 _27178)). Qed.
Lemma lem1156074 {_27176 _27178 : Type'} : (term23 _27176 _27178) = (term24 _27176 _27178).
Proof. exact (MK_COMB (@lem1156062 _27176 _27178) (@lem1156073 _27176 _27178)). Qed.
Lemma lem1156075 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1156076 {_27176 _27178 : Type'} : (term25 _27176 _27178) = (term26 _27176 _27178).
Proof. exact (MK_COMB (@lem1156075) (@lem1156074 _27176 _27178)). Qed.
Lemma lem1156077 {_27176 _27178 : Type'} (l1 : list _27176) : (term7 _27176 _27178 l1) = (term8 _27176 _27178 l1).
Proof. exact (eq_refl (term7 _27176 _27178 l1)). Qed.
Lemma lem1156078 {_27176 _27178 : Type'} : (term27 _27176 _27178) = (term2 _27176 _27178).
Proof. exact (fun_ext (fun l1 : list _27176 => @lem1156077 _27176 _27178 l1)). Qed.
Lemma lem1156079 {_27176 : Type'} : (@all (list _27176)) = (@all (list _27176)).
Proof. exact (eq_refl (@all (list _27176))). Qed.
Lemma lem1156080 {_27176 _27178 : Type'} : (term28 _27176 _27178) = (term29 _27176 _27178).
Proof. exact (MK_COMB (@lem1156079 _27176) (@lem1156078 _27176 _27178)). Qed.
Lemma lem1156081 {_27176 _27178 : Type'} : (term1 _27176 _27178) = (term30 _27176 _27178).
Proof. exact (MK_COMB (@lem1156076 _27176 _27178) (@lem1156080 _27176 _27178)). Qed.
Lemma lem1156082 {_27176 _27178 : Type'} : term30 _27176 _27178.
Proof. exact (EQ_MP (@lem1156081 _27176 _27178) (@lem1156059 _27176 _27178)). Qed.
Lemma lem1156083 {_27176 _27178 : Type'} (t : list _27176) (h1 : term8 _27176 _27178 t) : term8 _27176 _27178 t.
Proof. exact (h1). Qed.
Lemma lem1156085 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1156086 {_27178 : Type'} (P : type1143 _27178) : term0 _27178 P.
Proof. exact (@lem1156085 _27178 P). Qed.
Lemma lem1156087 {_27176 _27178 : Type'} : term31 _27176 _27178.
Proof. exact (@lem1156086 _27178 (term32 _27176 _27178)). Qed.
Lemma lem1156088 {_27176 _27178 : Type'} : (term33 _27176 _27178) = (term34 _27176 _27178).
Proof. exact (eq_refl (term33 _27176 _27178)). Qed.
Lemma lem1156089 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1156090 {_27176 _27178 : Type'} : (term35 _27176 _27178) = (term36 _27176 _27178).
Proof. exact (MK_COMB (@lem1156089) (@lem1156088 _27176 _27178)). Qed.
Lemma lem1156091 {_27176 _27178 : Type'} (t : list _27178) : (term37 _27176 _27178 t) = (term38 _27176 _27178 t).
Proof. exact (eq_refl (term37 _27176 _27178 t)). Qed.
Lemma lem1156092 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1156093 {_27176 _27178 : Type'} (t : list _27178) : (term39 _27176 _27178 t) = (term40 _27176 _27178 t).
Proof. exact (MK_COMB (@lem1156092) (@lem1156091 _27176 _27178 t)). Qed.
Lemma lem1156094 {_27176 _27178 : Type'} (h : _27178) (t : list _27178) : (term41 _27176 _27178 h t) = (term42 _27176 _27178 h t).
Proof. exact (eq_refl (term41 _27176 _27178 h t)). Qed.
Lemma lem1156095 {_27176 _27178 : Type'} (h : _27178) (t : list _27178) : (term43 _27176 _27178 h t) = (term44 _27176 _27178 h t).
Proof. exact (MK_COMB (@lem1156093 _27176 _27178 t) (@lem1156094 _27176 _27178 h t)). Qed.
Lemma lem1156096 {_27176 _27178 : Type'} (h : _27178) : (term45 _27176 _27178 h) = (term46 _27176 _27178 h).
Proof. exact (fun_ext (fun t : list _27178 => @lem1156095 _27176 _27178 h t)). Qed.
Lemma lem1156097 {_27178 : Type'} : (@all (list _27178)) = (@all (list _27178)).
Proof. exact (eq_refl (@all (list _27178))). Qed.
Lemma lem1156098 {_27176 _27178 : Type'} (h : _27178) : (term47 _27176 _27178 h) = (term48 _27176 _27178 h).
Proof. exact (MK_COMB (@lem1156097 _27178) (@lem1156096 _27176 _27178 h)). Qed.
Lemma lem1156099 {_27176 _27178 : Type'} : (term49 _27176 _27178) = (term50 _27176 _27178).
Proof. exact (fun_ext (fun h : _27178 => @lem1156098 _27176 _27178 h)). Qed.
Lemma lem1156100 {_27178 : Type'} : (@all _27178) = (@all _27178).
Proof. exact (eq_refl (@all _27178)). Qed.
Lemma lem1156101 {_27176 _27178 : Type'} : (term51 _27176 _27178) = (term52 _27176 _27178).
Proof. exact (MK_COMB (@lem1156100 _27178) (@lem1156099 _27176 _27178)). Qed.
Lemma lem1156102 {_27176 _27178 : Type'} : (term53 _27176 _27178) = (term54 _27176 _27178).
Proof. exact (MK_COMB (@lem1156090 _27176 _27178) (@lem1156101 _27176 _27178)). Qed.
Lemma lem1156103 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1156104 {_27176 _27178 : Type'} : (term55 _27176 _27178) = (term56 _27176 _27178).
Proof. exact (MK_COMB (@lem1156103) (@lem1156102 _27176 _27178)). Qed.
Lemma lem1156105 {_27176 _27178 : Type'} (l2 : list _27178) : (term37 _27176 _27178 l2) = (term38 _27176 _27178 l2).
Proof. exact (eq_refl (term37 _27176 _27178 l2)). Qed.
Lemma lem1156106 {_27176 _27178 : Type'} : (term57 _27176 _27178) = (term32 _27176 _27178).
Proof. exact (fun_ext (fun l2 : list _27178 => @lem1156105 _27176 _27178 l2)). Qed.
Lemma lem1156107 {_27178 : Type'} : (@all (list _27178)) = (@all (list _27178)).
Proof. exact (eq_refl (@all (list _27178))). Qed.
Lemma lem1156108 {_27176 _27178 : Type'} : (term58 _27176 _27178) = (term4 _27176 _27178).
Proof. exact (MK_COMB (@lem1156107 _27178) (@lem1156106 _27176 _27178)). Qed.
Lemma lem1156109 {_27176 _27178 : Type'} : (term31 _27176 _27178) = (term59 _27176 _27178).
Proof. exact (MK_COMB (@lem1156104 _27176 _27178) (@lem1156108 _27176 _27178)). Qed.
Lemma lem1156110 {_27176 _27178 : Type'} : term59 _27176 _27178.
Proof. exact (EQ_MP (@lem1156109 _27176 _27178) (@lem1156087 _27176 _27178)). Qed.
Lemma lem1156117 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1156118 {_27178 : Type'} (P : type1143 _27178) : term0 _27178 P.
Proof. exact (@lem1156117 _27178 P). Qed.
Lemma lem1156119 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) : term60 _27176 _27178 h t.
Proof. exact (@lem1156118 _27178 (term61 _27176 _27178 h t)). Qed.
Lemma lem1156120 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) : (term62 _27176 _27178 h t) = (term63 _27176 _27178 h t).
Proof. exact (eq_refl (term62 _27176 _27178 h t)). Qed.
Lemma lem1156121 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1156122 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) : (term64 _27176 _27178 h t) = (term65 _27176 _27178 h t).
Proof. exact (MK_COMB (@lem1156121) (@lem1156120 _27176 _27178 h t)). Qed.
Lemma lem1156123 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) (t' : list _27178) : (term66 _27176 _27178 h t t') = (term67 _27176 _27178 h t t').
Proof. exact (eq_refl (term66 _27176 _27178 h t t')). Qed.
Lemma lem1156124 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1156125 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) (t' : list _27178) : (term68 _27176 _27178 h t t') = (term69 _27176 _27178 h t t').
Proof. exact (MK_COMB (@lem1156124) (@lem1156123 _27176 _27178 h t t')). Qed.
Lemma lem1156126 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) (h' : _27178) (t' : list _27178) : (term70 _27176 _27178 h t h' t') = (term71 _27176 _27178 h t h' t').
Proof. exact (eq_refl (term70 _27176 _27178 h t h' t')). Qed.
Lemma lem1156127 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) (h' : _27178) (t' : list _27178) : (term72 _27176 _27178 h t h' t') = (term73 _27176 _27178 h t h' t').
Proof. exact (MK_COMB (@lem1156125 _27176 _27178 h t t') (@lem1156126 _27176 _27178 h t h' t')). Qed.
Lemma lem1156128 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) (h' : _27178) : (term74 _27176 _27178 h t h') = (term75 _27176 _27178 h t h').
Proof. exact (fun_ext (fun t' : list _27178 => @lem1156127 _27176 _27178 h t h' t')). Qed.
Lemma lem1156129 {_27178 : Type'} : (@all (list _27178)) = (@all (list _27178)).
Proof. exact (eq_refl (@all (list _27178))). Qed.
Lemma lem1156130 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) (h' : _27178) : (term76 _27176 _27178 h t h') = (term77 _27176 _27178 h t h').
Proof. exact (MK_COMB (@lem1156129 _27178) (@lem1156128 _27176 _27178 h t h')). Qed.
Lemma lem1156131 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) : (term78 _27176 _27178 h t) = (term79 _27176 _27178 h t).
Proof. exact (fun_ext (fun h' : _27178 => @lem1156130 _27176 _27178 h t h')). Qed.
Lemma lem1156132 {_27178 : Type'} : (@all _27178) = (@all _27178).
Proof. exact (eq_refl (@all _27178)). Qed.
Lemma lem1156133 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) : (term80 _27176 _27178 h t) = (term81 _27176 _27178 h t).
Proof. exact (MK_COMB (@lem1156132 _27178) (@lem1156131 _27176 _27178 h t)). Qed.
Lemma lem1156134 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) : (term82 _27176 _27178 h t) = (term83 _27176 _27178 h t).
Proof. exact (MK_COMB (@lem1156122 _27176 _27178 h t) (@lem1156133 _27176 _27178 h t)). Qed.
Lemma lem1156135 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1156136 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) : (term84 _27176 _27178 h t) = (term85 _27176 _27178 h t).
Proof. exact (MK_COMB (@lem1156135) (@lem1156134 _27176 _27178 h t)). Qed.
Lemma lem1156137 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) (l2 : list _27178) : (term66 _27176 _27178 h t l2) = (term67 _27176 _27178 h t l2).
Proof. exact (eq_refl (term66 _27176 _27178 h t l2)). Qed.
Lemma lem1156138 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) : (term86 _27176 _27178 h t) = (term61 _27176 _27178 h t).
Proof. exact (fun_ext (fun l2 : list _27178 => @lem1156137 _27176 _27178 h t l2)). Qed.
Lemma lem1156139 {_27178 : Type'} : (@all (list _27178)) = (@all (list _27178)).
Proof. exact (eq_refl (@all (list _27178))). Qed.
Lemma lem1156140 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) : (term87 _27176 _27178 h t) = (term12 _27176 _27178 h t).
Proof. exact (MK_COMB (@lem1156139 _27178) (@lem1156138 _27176 _27178 h t)). Qed.
Lemma lem1156141 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) : (term60 _27176 _27178 h t) = (term88 _27176 _27178 h t).
Proof. exact (MK_COMB (@lem1156136 _27176 _27178 h t) (@lem1156140 _27176 _27178 h t)). Qed.
Lemma lem1156142 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) : term88 _27176 _27178 h t.
Proof. exact (EQ_MP (@lem1156141 _27176 _27178 h t) (@lem1156119 _27176 _27178 h t)). Qed.
Lemma lem1156185 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term89 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1156186 (p : Prop) (q : Prop) (p' : Prop) : term90 p q p'.
Proof. exact (fun q' : Prop => @lem1156185 p q p' q'). Qed.
Lemma lem1156187 (p : Prop) (q : Prop) : term91 p q.
Proof. exact (fun p' : Prop => @lem1156186 p q p'). Qed.
Lemma lem1156188 {_27176 _27178 : Type'} : term92 _27176 _27178.
Proof. exact (@lem1156187 ((@List.length _27176 (@nil _27176)) = (@List.length _27178 (@nil _27178))) ((term93 _27176 _27178) = (@List.length _27178 (@nil _27178)))). Qed.
Lemma lem1156189 {_27176 _27178 : Type'} (p' : Prop) : term94 _27176 _27178 p'.
Proof. exact (@lem1156188 _27176 _27178 p'). Qed.
Lemma lem1156190 {_27176 _27178 : Type'} (p' : Prop) : (term94 _27176 _27178 p') = (term95 _27176 _27178 p').
Proof. exact (eq_refl (term94 _27176 _27178 p')). Qed.
Lemma lem1156191 {_27176 _27178 : Type'} (p' : Prop) : term95 _27176 _27178 p'.
Proof. exact (EQ_MP (@lem1156190 _27176 _27178 p') (@lem1156189 _27176 _27178 p')). Qed.
Lemma lem1156192 {_27176 _27178 : Type'} (p' : Prop) (q' : Prop) : term96 _27176 _27178 p' q'.
Proof. exact (@lem1156191 _27176 _27178 p' q'). Qed.
Lemma lem1156193 {_27176 _27178 : Type'} (p' : Prop) (q' : Prop) : (term96 _27176 _27178 p' q') = (term97 _27176 _27178 p' q').
Proof. exact (eq_refl (term96 _27176 _27178 p' q')). Qed.
Lemma lem1156194 {_27176 _27178 : Type'} (p' : Prop) (q' : Prop) : term97 _27176 _27178 p' q'.
Proof. exact (EQ_MP (@lem1156193 _27176 _27178 p' q') (@lem1156192 _27176 _27178 p' q')). Qed.
Lemma lem1156198 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1156199 {_27176 : Type'} : (@List.length _27176 (@nil _27176)) = (NUMERAL 0).
Proof. exact (@lem1156198 _27176). Qed.
Lemma lem1156200 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1156201 {_27176 : Type'} : (term98 _27176) = term99.
Proof. exact (MK_COMB (@lem1156200) (@lem1156199 _27176)). Qed.
Lemma lem1156203 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1156204 {_27178 : Type'} : (@List.length _27178 (@nil _27178)) = (NUMERAL 0).
Proof. exact (@lem1156203 _27178). Qed.
Lemma lem1156205 {_27176 _27178 : Type'} : ((@List.length _27176 (@nil _27176)) = (@List.length _27178 (@nil _27178))) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1156201 _27176) (@lem1156204 _27178)). Qed.
Lemma lem1156207 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1156208 (x : nat) : (x = x) = True.
Proof. exact (@lem1156207 nat x). Qed.
Lemma lem1156209 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1156208 (NUMERAL 0)). Qed.
Lemma lem1156210 {_27176 _27178 : Type'} : ((@List.length _27176 (@nil _27176)) = (@List.length _27178 (@nil _27178))) = True.
Proof. exact (TRANS (@lem1156205 _27176 _27178) (@lem1156209)). Qed.
Lemma lem1156211 {_27176 _27178 : Type'} (q' : Prop) : term100 _27176 _27178 q'.
Proof. exact (@lem1156194 _27176 _27178 True q'). Qed.
Lemma lem1156212 {_27176 _27178 : Type'} (q' : Prop) : term101 _27176 _27178 q'.
Proof. exact (@lem1156211 _27176 _27178 q' (@lem1156210 _27176 _27178)). Qed.
Lemma lem1156221 {_25738 _25739 : Type'} : (@ZIP _25738 _25739 (@nil _25738) (@nil _25739)) = (@nil (prod _25738 _25739)).
Proof. exact (proj1 (@lem1109008 _25738 _25739 Prop Prop (@el Prop) (@el Prop) (@el (list Prop)) (@el (list Prop)))). Qed.
Lemma lem1156222 {_27176 _27178 : Type'} : (@ZIP _27176 _27178 (@nil _27176) (@nil _27178)) = (@nil (prod _27176 _27178)).
Proof. exact (@lem1156221 _27176 _27178). Qed.
Lemma lem1156223 {_27176 _27178 : Type'} : (@List.length (prod _27176 _27178)) = (@List.length (prod _27176 _27178)).
Proof. exact (eq_refl (@List.length (prod _27176 _27178))). Qed.
Lemma lem1156224 {_27176 _27178 : Type'} : (term93 _27176 _27178) = (@List.length (prod _27176 _27178) (@nil (prod _27176 _27178))).
Proof. exact (MK_COMB (@lem1156223 _27176 _27178) (@lem1156222 _27176 _27178)). Qed.
Lemma lem1156226 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1156227 {_27176 _27178 : Type'} : (@List.length (prod _27176 _27178) (@nil (prod _27176 _27178))) = (NUMERAL 0).
Proof. exact (@lem1156226 (prod _27176 _27178)). Qed.
Lemma lem1156228 {_27176 _27178 : Type'} : (term93 _27176 _27178) = (NUMERAL 0).
Proof. exact (TRANS (@lem1156224 _27176 _27178) (@lem1156227 _27176 _27178)). Qed.
Lemma lem1156229 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1156230 {_27176 _27178 : Type'} : (term102 _27176 _27178) = term99.
Proof. exact (MK_COMB (@lem1156229) (@lem1156228 _27176 _27178)). Qed.
Lemma lem1156232 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1156233 {_27178 : Type'} : (@List.length _27178 (@nil _27178)) = (NUMERAL 0).
Proof. exact (@lem1156232 _27178). Qed.
Lemma lem1156234 {_27176 _27178 : Type'} : ((term93 _27176 _27178) = (@List.length _27178 (@nil _27178))) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1156230 _27176 _27178) (@lem1156233 _27178)). Qed.
Lemma lem1156236 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1156237 (x : nat) : (x = x) = True.
Proof. exact (@lem1156236 nat x). Qed.
Lemma lem1156238 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1156237 (NUMERAL 0)). Qed.
Lemma lem1156241 {_27176 _27178 : Type'} : ((term93 _27176 _27178) = (@List.length _27178 (@nil _27178))) = True.
Proof. exact (TRANS (@lem1156234 _27176 _27178) (@lem1156238)). Qed.
Lemma lem1156242 {_27176 _27178 : Type'} : term103 _27176 _27178.
Proof. exact (fun h0 : True => @lem1156241 _27176 _27178). Qed.
Lemma lem1156243 {_27176 _27178 : Type'} : term104 _27176 _27178.
Proof. exact (@lem1156212 _27176 _27178 True). Qed.
Lemma lem1156244 {_27176 _27178 : Type'} : (term34 _27176 _27178) = (True -> True).
Proof. exact (@lem1156243 _27176 _27178 (@lem1156242 _27176 _27178)). Qed.
Lemma lem1156246 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1156247 : (True -> True) = True.
Proof. exact (@lem1156246 True). Qed.
Lemma lem1156248 {_27176 _27178 : Type'} : (term34 _27176 _27178) = True.
Proof. exact (TRANS (@lem1156244 _27176 _27178) (@lem1156247)). Qed.
Lemma lem1156249 {_27176 _27178 : Type'} : True = (term34 _27176 _27178).
Proof. exact (SYM (@lem1156248 _27176 _27178)). Qed.
Lemma lem1156250 {_27176 _27178 : Type'} : term34 _27176 _27178.
Proof. exact (EQ_MP (@lem1156249 _27176 _27178) (@lem0)). Qed.
Lemma lem1156259 (n : nat) : term105 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem1156260 (n : nat) : (term105 n) = (term106 n).
Proof. exact (eq_refl (term105 n)). Qed.
Lemma lem1156261 (n : nat) : term106 n.
Proof. exact (EQ_MP (@lem1156260 n) (@lem1156259 n)). Qed.
Lemma lem1156265 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (S n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1156266 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (NUMERAL 0) = (S n).
Proof. exact (SYM (@lem1156265 n h1)). Qed.
Lemma lem1156267 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (NUMERAL 0) = (S n).
Proof. exact (h1). Qed.
Lemma lem1156268 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (S n) = (NUMERAL 0).
Proof. exact (SYM (@lem1156267 n h1)). Qed.
Lemma lem1156269 (n : nat) : ((S n) = (NUMERAL 0)) = ((NUMERAL 0) = (S n)).
Proof. exact (prop_ext (fun h1 : (S n) = (NUMERAL 0) => @lem1156266 n h1) (fun h1 : (NUMERAL 0) = (S n) => @lem1156268 n h1)). Qed.
Lemma lem1156270 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1156271 (n : nat) : (term106 n) = (term107 n).
Proof. exact (MK_COMB (@lem1156270) (@lem1156269 n)). Qed.
Lemma lem1156272 (n : nat) : term107 n.
Proof. exact (EQ_MP (@lem1156271 n) (@lem1156261 n)). Qed.
Lemma lem1156273 (n : nat) : term108 n.
Proof. exact (@lem82 ((NUMERAL 0) = (S n))). Qed.
Lemma lem1156275 {A : Type'} : term109 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1156276 {A : Type'} (h : A) : term110 A h.
Proof. exact (@lem1156275 A h). Qed.
Lemma lem1156277 {A : Type'} (h : A) : (term110 A h) = (term111 A h).
Proof. exact (eq_refl (term110 A h)). Qed.
Lemma lem1156278 {A : Type'} (h : A) : term111 A h.
Proof. exact (EQ_MP (@lem1156277 A h) (@lem1156276 A h)). Qed.
Lemma lem1156279 {A : Type'} (h : A) (t : list A) : term112 A h t.
Proof. exact (@lem1156278 A h t). Qed.
Lemma lem1156280 {A : Type'} (h : A) (t : list A) : (term112 A h t) = ((term113 A h t) = (term114 A t)).
Proof. exact (eq_refl (term112 A h t)). Qed.
Lemma lem1156295 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term89 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1156296 (p : Prop) (q : Prop) (p' : Prop) : term90 p q p'.
Proof. exact (fun q' : Prop => @lem1156295 p q p' q'). Qed.
Lemma lem1156297 (p : Prop) (q : Prop) : term91 p q.
Proof. exact (fun p' : Prop => @lem1156296 p q p'). Qed.
Lemma lem1156298 {_27176 _27178 : Type'} (h : _27178) (t : list _27178) : term115 _27176 _27178 h t.
Proof. exact (@lem1156297 ((@List.length _27176 (@nil _27176)) = (term113 _27178 h t)) ((term116 _27176 _27178 h t) = (term113 _27178 h t))). Qed.
Lemma lem1156299 {_27176 _27178 : Type'} (h : _27178) (t : list _27178) (p' : Prop) : term117 _27176 _27178 h t p'.
Proof. exact (@lem1156298 _27176 _27178 h t p'). Qed.
Lemma lem1156300 {_27176 _27178 : Type'} (h : _27178) (t : list _27178) (p' : Prop) : (term117 _27176 _27178 h t p') = (term118 _27176 _27178 h t p').
Proof. exact (eq_refl (term117 _27176 _27178 h t p')). Qed.
Lemma lem1156301 {_27176 _27178 : Type'} (h : _27178) (t : list _27178) (p' : Prop) : term118 _27176 _27178 h t p'.
Proof. exact (EQ_MP (@lem1156300 _27176 _27178 h t p') (@lem1156299 _27176 _27178 h t p')). Qed.
Lemma lem1156302 {_27176 _27178 : Type'} (h : _27178) (t : list _27178) (p' : Prop) (q' : Prop) : term119 _27176 _27178 h t p' q'.
Proof. exact (@lem1156301 _27176 _27178 h t p' q'). Qed.
Lemma lem1156303 {_27176 _27178 : Type'} (h : _27178) (t : list _27178) (p' : Prop) (q' : Prop) : (term119 _27176 _27178 h t p' q') = (term120 _27176 _27178 h t p' q').
Proof. exact (eq_refl (term119 _27176 _27178 h t p' q')). Qed.
Lemma lem1156304 {_27176 _27178 : Type'} (h : _27178) (t : list _27178) (p' : Prop) (q' : Prop) : term120 _27176 _27178 h t p' q'.
Proof. exact (EQ_MP (@lem1156303 _27176 _27178 h t p' q') (@lem1156302 _27176 _27178 h t p' q')). Qed.
Lemma lem1156308 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1156309 {_27176 : Type'} : (@List.length _27176 (@nil _27176)) = (NUMERAL 0).
Proof. exact (@lem1156308 _27176). Qed.
Lemma lem1156310 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1156311 {_27176 : Type'} : (term98 _27176) = term99.
Proof. exact (MK_COMB (@lem1156310) (@lem1156309 _27176)). Qed.
Lemma lem1156313 {A : Type'} (h : A) (t : list A) : (term113 A h t) = (term114 A t).
Proof. exact (EQ_MP (@lem1156280 A h t) (@lem1156279 A h t)). Qed.
Lemma lem1156314 {_27178 : Type'} (h : _27178) (t : list _27178) : (term113 _27178 h t) = (term114 _27178 t).
Proof. exact (@lem1156313 _27178 h t). Qed.
Lemma lem1156315 {_27176 _27178 : Type'} (h : _27178) (t : list _27178) : ((@List.length _27176 (@nil _27176)) = (term113 _27178 h t)) = ((NUMERAL 0) = (term114 _27178 t)).
Proof. exact (MK_COMB (@lem1156311 _27176) (@lem1156314 _27178 h t)). Qed.
Lemma lem1156317 (n : nat) : ((NUMERAL 0) = (S n)) = False.
Proof. exact (@lem1156273 n (@lem1156272 n)). Qed.
Lemma lem1156318 {_27178 : Type'} (t : list _27178) : ((NUMERAL 0) = (term114 _27178 t)) = False.
Proof. exact (@lem1156317 (@List.length _27178 t)). Qed.
Lemma lem1156319 {_27176 _27178 : Type'} (h : _27178) (t : list _27178) : ((@List.length _27176 (@nil _27176)) = (term113 _27178 h t)) = False.
Proof. exact (TRANS (@lem1156315 _27176 _27178 h t) (@lem1156318 _27178 t)). Qed.
Lemma lem1156320 {_27176 _27178 : Type'} (h : _27178) (t : list _27178) (q' : Prop) : term121 _27176 _27178 h t q'.
Proof. exact (@lem1156304 _27176 _27178 h t False q'). Qed.
Lemma lem1156321 {_27176 _27178 : Type'} (h : _27178) (t : list _27178) (q' : Prop) : term122 _27176 _27178 h t q'.
Proof. exact (@lem1156320 _27176 _27178 h t q' (@lem1156319 _27176 _27178 h t)). Qed.
Lemma lem1156328 {A : Type'} (h : A) (t : list A) : (term113 A h t) = (term114 A t).
Proof. exact (EQ_MP (@lem1156280 A h t) (@lem1156279 A h t)). Qed.
Lemma lem1156329 {_27178 : Type'} (h : _27178) (t : list _27178) : (term113 _27178 h t) = (term114 _27178 t).
Proof. exact (@lem1156328 _27178 h t). Qed.
Lemma lem1156330 {_27176 _27178 : Type'} (h : _27178) (t : list _27178) : (term123 _27176 _27178 h t) = (term123 _27176 _27178 h t).
Proof. exact (eq_refl (term123 _27176 _27178 h t)). Qed.
Lemma lem1156331 {_27176 _27178 : Type'} (h : _27178) (t : list _27178) : ((term116 _27176 _27178 h t) = (term113 _27178 h t)) = ((term116 _27176 _27178 h t) = (term114 _27178 t)).
Proof. exact (MK_COMB (@lem1156330 _27176 _27178 h t) (@lem1156329 _27178 h t)). Qed.
Lemma lem1156334 {_27176 _27178 : Type'} (h : _27178) (t : list _27178) : term124 _27176 _27178 h t.
Proof. exact (fun h0 : False => @lem1156331 _27176 _27178 h t). Qed.
Lemma lem1156335 {_27176 _27178 : Type'} (h : _27178) (t : list _27178) : term125 _27176 _27178 h t.
Proof. exact (@lem1156321 _27176 _27178 h t ((term116 _27176 _27178 h t) = (term114 _27178 t))). Qed.
Lemma lem1156336 {_27176 _27178 : Type'} (h : _27178) (t : list _27178) : (term42 _27176 _27178 h t) = (term126 _27176 _27178 h t).
Proof. exact (@lem1156335 _27176 _27178 h t (@lem1156334 _27176 _27178 h t)). Qed.
Lemma lem1156338 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1156339 {_27176 _27178 : Type'} (h : _27178) (t : list _27178) : (term126 _27176 _27178 h t) = True.
Proof. exact (@lem1156338 ((term116 _27176 _27178 h t) = (term114 _27178 t))). Qed.
Lemma lem1156340 {_27176 _27178 : Type'} (h : _27178) (t : list _27178) : (term42 _27176 _27178 h t) = True.
Proof. exact (TRANS (@lem1156336 _27176 _27178 h t) (@lem1156339 _27176 _27178 h t)). Qed.
Lemma lem1156341 {_27176 _27178 : Type'} (h : _27178) (t : list _27178) : True = (term42 _27176 _27178 h t).
Proof. exact (SYM (@lem1156340 _27176 _27178 h t)). Qed.
Lemma lem1156342 {_27176 _27178 : Type'} (h : _27178) (t : list _27178) : term42 _27176 _27178 h t.
Proof. exact (EQ_MP (@lem1156341 _27176 _27178 h t) (@lem0)). Qed.
Lemma lem1156351 (n : nat) : term105 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem1156352 (n : nat) : (term105 n) = (term106 n).
Proof. exact (eq_refl (term105 n)). Qed.
Lemma lem1156353 (n : nat) : term106 n.
Proof. exact (EQ_MP (@lem1156352 n) (@lem1156351 n)). Qed.
Lemma lem1156354 (n : nat) : term127 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem1156367 {A : Type'} : term109 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1156368 {A : Type'} (h : A) : term110 A h.
Proof. exact (@lem1156367 A h). Qed.
Lemma lem1156369 {A : Type'} (h : A) : (term110 A h) = (term111 A h).
Proof. exact (eq_refl (term110 A h)). Qed.
Lemma lem1156370 {A : Type'} (h : A) : term111 A h.
Proof. exact (EQ_MP (@lem1156369 A h) (@lem1156368 A h)). Qed.
Lemma lem1156371 {A : Type'} (h : A) (t : list A) : term112 A h t.
Proof. exact (@lem1156370 A h t). Qed.
Lemma lem1156372 {A : Type'} (h : A) (t : list A) : (term112 A h t) = ((term113 A h t) = (term114 A t)).
Proof. exact (eq_refl (term112 A h t)). Qed.
Lemma lem1156390 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term89 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1156391 (p : Prop) (q : Prop) (p' : Prop) : term90 p q p'.
Proof. exact (fun q' : Prop => @lem1156390 p q p' q'). Qed.
Lemma lem1156392 (p : Prop) (q : Prop) : term91 p q.
Proof. exact (fun p' : Prop => @lem1156391 p q p'). Qed.
Lemma lem1156393 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) : term128 _27176 _27178 h t.
Proof. exact (@lem1156392 ((term113 _27176 h t) = (@List.length _27178 (@nil _27178))) ((term129 _27176 _27178 h t) = (@List.length _27178 (@nil _27178)))). Qed.
Lemma lem1156394 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) (p' : Prop) : term130 _27176 _27178 h t p'.
Proof. exact (@lem1156393 _27176 _27178 h t p'). Qed.
Lemma lem1156395 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) (p' : Prop) : (term130 _27176 _27178 h t p') = (term131 _27176 _27178 h t p').
Proof. exact (eq_refl (term130 _27176 _27178 h t p')). Qed.
Lemma lem1156396 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) (p' : Prop) : term131 _27176 _27178 h t p'.
Proof. exact (EQ_MP (@lem1156395 _27176 _27178 h t p') (@lem1156394 _27176 _27178 h t p')). Qed.
Lemma lem1156397 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) (p' : Prop) (q' : Prop) : term132 _27176 _27178 h t p' q'.
Proof. exact (@lem1156396 _27176 _27178 h t p' q'). Qed.
Lemma lem1156398 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) (p' : Prop) (q' : Prop) : (term132 _27176 _27178 h t p' q') = (term133 _27176 _27178 h t p' q').
Proof. exact (eq_refl (term132 _27176 _27178 h t p' q')). Qed.
Lemma lem1156399 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) (p' : Prop) (q' : Prop) : term133 _27176 _27178 h t p' q'.
Proof. exact (EQ_MP (@lem1156398 _27176 _27178 h t p' q') (@lem1156397 _27176 _27178 h t p' q')). Qed.
Lemma lem1156403 {A : Type'} (h : A) (t : list A) : (term113 A h t) = (term114 A t).
Proof. exact (EQ_MP (@lem1156372 A h t) (@lem1156371 A h t)). Qed.
Lemma lem1156404 {_27176 : Type'} (h : _27176) (t : list _27176) : (term113 _27176 h t) = (term114 _27176 t).
Proof. exact (@lem1156403 _27176 h t). Qed.
Lemma lem1156405 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1156406 {_27176 : Type'} (h : _27176) (t : list _27176) : (term134 _27176 h t) = (term135 _27176 t).
Proof. exact (MK_COMB (@lem1156405) (@lem1156404 _27176 h t)). Qed.
Lemma lem1156408 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1156409 {_27178 : Type'} : (@List.length _27178 (@nil _27178)) = (NUMERAL 0).
Proof. exact (@lem1156408 _27178). Qed.
Lemma lem1156410 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) : ((term113 _27176 h t) = (@List.length _27178 (@nil _27178))) = ((term114 _27176 t) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1156406 _27176 h t) (@lem1156409 _27178)). Qed.
Lemma lem1156412 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1156354 n (@lem1156353 n)). Qed.
Lemma lem1156413 {_27176 : Type'} (t : list _27176) : ((term114 _27176 t) = (NUMERAL 0)) = False.
Proof. exact (@lem1156412 (@List.length _27176 t)). Qed.
Lemma lem1156414 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) : ((term113 _27176 h t) = (@List.length _27178 (@nil _27178))) = False.
Proof. exact (TRANS (@lem1156410 _27176 _27178 h t) (@lem1156413 _27176 t)). Qed.
Lemma lem1156415 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) (q' : Prop) : term136 _27176 _27178 h t q'.
Proof. exact (@lem1156399 _27176 _27178 h t False q'). Qed.
Lemma lem1156416 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) (q' : Prop) : term137 _27176 _27178 h t q'.
Proof. exact (@lem1156415 _27176 _27178 h t q' (@lem1156414 _27176 _27178 h t)). Qed.
Lemma lem1156423 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1156424 {_27178 : Type'} : (@List.length _27178 (@nil _27178)) = (NUMERAL 0).
Proof. exact (@lem1156423 _27178). Qed.
Lemma lem1156425 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) : (term138 _27176 _27178 h t) = (term138 _27176 _27178 h t).
Proof. exact (eq_refl (term138 _27176 _27178 h t)). Qed.
Lemma lem1156426 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) : ((term129 _27176 _27178 h t) = (@List.length _27178 (@nil _27178))) = ((term129 _27176 _27178 h t) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1156425 _27176 _27178 h t) (@lem1156424 _27178)). Qed.
Lemma lem1156429 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) : term139 _27176 _27178 h t.
Proof. exact (fun h0 : False => @lem1156426 _27176 _27178 h t). Qed.
Lemma lem1156430 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) : term140 _27176 _27178 h t.
Proof. exact (@lem1156416 _27176 _27178 h t ((term129 _27176 _27178 h t) = (NUMERAL 0))). Qed.
Lemma lem1156431 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) : (term63 _27176 _27178 h t) = (term141 _27176 _27178 h t).
Proof. exact (@lem1156430 _27176 _27178 h t (@lem1156429 _27176 _27178 h t)). Qed.
Lemma lem1156433 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1156434 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) : (term141 _27176 _27178 h t) = True.
Proof. exact (@lem1156433 ((term129 _27176 _27178 h t) = (NUMERAL 0))). Qed.
Lemma lem1156435 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) : (term63 _27176 _27178 h t) = True.
Proof. exact (TRANS (@lem1156431 _27176 _27178 h t) (@lem1156434 _27176 _27178 h t)). Qed.
Lemma lem1156436 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) : True = (term63 _27176 _27178 h t).
Proof. exact (SYM (@lem1156435 _27176 _27178 h t)). Qed.
Lemma lem1156437 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) : term63 _27176 _27178 h t.
Proof. exact (EQ_MP (@lem1156436 _27176 _27178 h t) (@lem0)). Qed.
Lemma lem1156438 (m : nat) : term142 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem1156439 (m : nat) : (term142 m) = (term143 m).
Proof. exact (eq_refl (term142 m)). Qed.
Lemma lem1156440 (m : nat) : term143 m.
Proof. exact (EQ_MP (@lem1156439 m) (@lem1156438 m)). Qed.
Lemma lem1156441 (m : nat) (n : nat) : term144 m n.
Proof. exact (@lem1156440 m n). Qed.
Lemma lem1156442 (m : nat) (n : nat) : (term144 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term144 m n)). Qed.
Lemma lem1156462 {A : Type'} : term109 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1156463 {A : Type'} (h : A) : term110 A h.
Proof. exact (@lem1156462 A h). Qed.
Lemma lem1156464 {A : Type'} (h : A) : (term110 A h) = (term111 A h).
Proof. exact (eq_refl (term110 A h)). Qed.
Lemma lem1156465 {A : Type'} (h : A) : term111 A h.
Proof. exact (EQ_MP (@lem1156464 A h) (@lem1156463 A h)). Qed.
Lemma lem1156466 {A : Type'} (h : A) (t : list A) : term112 A h t.
Proof. exact (@lem1156465 A h t). Qed.
Lemma lem1156467 {A : Type'} (h : A) (t : list A) : (term112 A h t) = ((term113 A h t) = (term114 A t)).
Proof. exact (eq_refl (term112 A h t)). Qed.
Lemma lem1156470 {_27176 _27178 : Type'} (l2 : list _27178) (t : list _27176) (h1 : term8 _27176 _27178 t) : term145 _27176 _27178 t l2.
Proof. exact (@lem1156083 _27176 _27178 t h1 l2). Qed.
Lemma lem1156471 {_27176 _27178 : Type'} (t : list _27176) (l2 : list _27178) : (term145 _27176 _27178 t l2) = (term146 _27176 _27178 t l2).
Proof. exact (eq_refl (term145 _27176 _27178 t l2)). Qed.
Lemma lem1156472 {_27176 _27178 : Type'} (l2 : list _27178) (t : list _27176) (h1 : term8 _27176 _27178 t) : term146 _27176 _27178 t l2.
Proof. exact (EQ_MP (@lem1156471 _27176 _27178 t l2) (@lem1156470 _27176 _27178 l2 t h1)). Qed.
Lemma lem1156473 {_27176 _27178 : Type'} (t : list _27176) (l2 : list _27178) (h1 : (@List.length _27176 t) = (@List.length _27178 l2)) : (@List.length _27176 t) = (@List.length _27178 l2).
Proof. exact (h1). Qed.
Lemma lem1156474 {_27176 _27178 : Type'} (t : list _27176) (l2 : list _27178) (h1 : term8 _27176 _27178 t) (h2 : (@List.length _27176 t) = (@List.length _27178 l2)) : (term147 _27176 _27178 t l2) = (@List.length _27178 l2).
Proof. exact (@lem1156472 _27176 _27178 l2 t h1 (@lem1156473 _27176 _27178 t l2 h2)). Qed.
Lemma lem1156492 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term89 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1156493 (p : Prop) (q : Prop) (p' : Prop) : term90 p q p'.
Proof. exact (fun q' : Prop => @lem1156492 p q p' q'). Qed.
Lemma lem1156494 (p : Prop) (q : Prop) : term91 p q.
Proof. exact (fun p' : Prop => @lem1156493 p q p'). Qed.
Lemma lem1156495 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) (h' : _27178) (t' : list _27178) : term148 _27176 _27178 h t h' t'.
Proof. exact (@lem1156494 ((term113 _27176 h t) = (term113 _27178 h' t')) ((term149 _27176 _27178 h t h' t') = (term113 _27178 h' t'))). Qed.
Lemma lem1156496 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) (h' : _27178) (t' : list _27178) (p' : Prop) : term150 _27176 _27178 h t h' t' p'.
Proof. exact (@lem1156495 _27176 _27178 h t h' t' p'). Qed.
Lemma lem1156497 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) (h' : _27178) (t' : list _27178) (p' : Prop) : (term150 _27176 _27178 h t h' t' p') = (term151 _27176 _27178 h t h' t' p').
Proof. exact (eq_refl (term150 _27176 _27178 h t h' t' p')). Qed.
Lemma lem1156498 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) (h' : _27178) (t' : list _27178) (p' : Prop) : term151 _27176 _27178 h t h' t' p'.
Proof. exact (EQ_MP (@lem1156497 _27176 _27178 h t h' t' p') (@lem1156496 _27176 _27178 h t h' t' p')). Qed.
Lemma lem1156499 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) (h' : _27178) (t' : list _27178) (p' : Prop) (q' : Prop) : term152 _27176 _27178 h t h' t' p' q'.
Proof. exact (@lem1156498 _27176 _27178 h t h' t' p' q'). Qed.
Lemma lem1156500 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) (h' : _27178) (t' : list _27178) (p' : Prop) (q' : Prop) : (term152 _27176 _27178 h t h' t' p' q') = (term153 _27176 _27178 h t h' t' p' q').
Proof. exact (eq_refl (term152 _27176 _27178 h t h' t' p' q')). Qed.
Lemma lem1156501 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) (h' : _27178) (t' : list _27178) (p' : Prop) (q' : Prop) : term153 _27176 _27178 h t h' t' p' q'.
Proof. exact (EQ_MP (@lem1156500 _27176 _27178 h t h' t' p' q') (@lem1156499 _27176 _27178 h t h' t' p' q')). Qed.
Lemma lem1156505 {A : Type'} (h : A) (t : list A) : (term113 A h t) = (term114 A t).
Proof. exact (EQ_MP (@lem1156467 A h t) (@lem1156466 A h t)). Qed.
Lemma lem1156506 {_27176 : Type'} (h : _27176) (t : list _27176) : (term113 _27176 h t) = (term114 _27176 t).
Proof. exact (@lem1156505 _27176 h t). Qed.
Lemma lem1156507 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1156508 {_27176 : Type'} (h : _27176) (t : list _27176) : (term134 _27176 h t) = (term135 _27176 t).
Proof. exact (MK_COMB (@lem1156507) (@lem1156506 _27176 h t)). Qed.
Lemma lem1156510 {A : Type'} (h : A) (t : list A) : (term113 A h t) = (term114 A t).
Proof. exact (EQ_MP (@lem1156467 A h t) (@lem1156466 A h t)). Qed.
Lemma lem1156511 {_27178 : Type'} (h : _27178) (t : list _27178) : (term113 _27178 h t) = (term114 _27178 t).
Proof. exact (@lem1156510 _27178 h t). Qed.
Lemma lem1156512 {_27178 : Type'} (h' : _27178) (t' : list _27178) : (term113 _27178 h' t') = (term114 _27178 t').
Proof. exact (@lem1156511 _27178 h' t'). Qed.
Lemma lem1156513 {_27176 _27178 : Type'} (h : _27176) (h' : _27178) (t : list _27176) (t' : list _27178) : ((term113 _27176 h t) = (term113 _27178 h' t')) = ((term114 _27176 t) = (term114 _27178 t')).
Proof. exact (MK_COMB (@lem1156508 _27176 h t) (@lem1156512 _27178 h' t')). Qed.
Lemma lem1156515 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem1156442 m n) (@lem1156441 m n)). Qed.
Lemma lem1156516 {_27176 _27178 : Type'} (t : list _27176) (t' : list _27178) : ((term114 _27176 t) = (term114 _27178 t')) = ((@List.length _27176 t) = (@List.length _27178 t')).
Proof. exact (@lem1156515 (@List.length _27176 t) (@List.length _27178 t')). Qed.
Lemma lem1156519 {_27176 _27178 : Type'} (h : _27176) (h' : _27178) (t : list _27176) (t' : list _27178) : ((term113 _27176 h t) = (term113 _27178 h' t')) = ((@List.length _27176 t) = (@List.length _27178 t')).
Proof. exact (TRANS (@lem1156513 _27176 _27178 h h' t t') (@lem1156516 _27176 _27178 t t')). Qed.
Lemma lem1156520 {_27176 _27178 : Type'} (h : _27176) (h' : _27178) (t : list _27176) (t' : list _27178) (q' : Prop) : term154 _27176 _27178 h h' t t' q'.
Proof. exact (@lem1156501 _27176 _27178 h t h' t' ((@List.length _27176 t) = (@List.length _27178 t')) q'). Qed.
Lemma lem1156521 {_27176 _27178 : Type'} (h : _27176) (h' : _27178) (t : list _27176) (t' : list _27178) (q' : Prop) : term155 _27176 _27178 h h' t t' q'.
Proof. exact (@lem1156520 _27176 _27178 h h' t t' q' (@lem1156519 _27176 _27178 h h' t t')). Qed.
Lemma lem1156526 {_25763 _25764 : Type'} (h1' : _25763) (h2' : _25764) (t1 : list _25763) (t2 : list _25764) : (term156 _25763 _25764 h1' t1 h2' t2) = (term157 _25763 _25764 h1' h2' t1 t2).
Proof. exact (proj2 (@lem1109008 Prop Prop _25763 _25764 h1' h2' t1 t2)). Qed.
Lemma lem1156527 {_27176 _27178 : Type'} (h1' : _27176) (h2' : _27178) (t1 : list _27176) (t2 : list _27178) : (term156 _27176 _27178 h1' t1 h2' t2) = (term157 _27176 _27178 h1' h2' t1 t2).
Proof. exact (@lem1156526 _27176 _27178 h1' h2' t1 t2). Qed.
Lemma lem1156528 {_27176 _27178 : Type'} (h : _27176) (h' : _27178) (t : list _27176) (t' : list _27178) : (term156 _27176 _27178 h t h' t') = (term157 _27176 _27178 h h' t t').
Proof. exact (@lem1156527 _27176 _27178 h h' t t'). Qed.
Lemma lem1156529 {_27176 _27178 : Type'} : (@List.length (prod _27176 _27178)) = (@List.length (prod _27176 _27178)).
Proof. exact (eq_refl (@List.length (prod _27176 _27178))). Qed.
Lemma lem1156530 {_27176 _27178 : Type'} (h : _27176) (h' : _27178) (t : list _27176) (t' : list _27178) : (term149 _27176 _27178 h t h' t') = (term158 _27176 _27178 h h' t t').
Proof. exact (MK_COMB (@lem1156529 _27176 _27178) (@lem1156528 _27176 _27178 h h' t t')). Qed.
Lemma lem1156532 {A : Type'} (h : A) (t : list A) : (term113 A h t) = (term114 A t).
Proof. exact (EQ_MP (@lem1156467 A h t) (@lem1156466 A h t)). Qed.
Lemma lem1156533 {_27176 _27178 : Type'} (h : prod _27176 _27178) (t : type1640 _27176 _27178) : (term159 _27176 _27178 h t) = (term160 _27176 _27178 t).
Proof. exact (@lem1156532 (prod _27176 _27178) h t). Qed.
Lemma lem1156534 {_27176 _27178 : Type'} (h : _27176) (h' : _27178) (t : list _27176) (t' : list _27178) : (term158 _27176 _27178 h h' t t') = (term161 _27176 _27178 t t').
Proof. exact (@lem1156533 _27176 _27178 (@pair _27176 _27178 h h') (@ZIP _27176 _27178 t t')). Qed.
Lemma lem1156536 {_27176 _27178 : Type'} (l2 : list _27178) (t : list _27176) (h1 : term8 _27176 _27178 t) : term146 _27176 _27178 t l2.
Proof. exact (fun h0 : (@List.length _27176 t) = (@List.length _27178 l2) => @lem1156474 _27176 _27178 t l2 h1 h0). Qed.
Lemma lem1156537 {_27176 _27178 : Type'} (l2 : list _27178) (t : list _27176) (h1 : term8 _27176 _27178 t) : term146 _27176 _27178 t l2.
Proof. exact (@lem1156536 _27176 _27178 l2 t h1). Qed.
Lemma lem1156538 {_27176 _27178 : Type'} (t' : list _27178) (t : list _27176) (h1 : term8 _27176 _27178 t) : term146 _27176 _27178 t t'.
Proof. exact (@lem1156537 _27176 _27178 t' t h1). Qed.
Lemma lem1156542 {_27176 _27178 : Type'} (t : list _27176) (t' : list _27178) (h1 : (@List.length _27176 t) = (@List.length _27178 t')) : (@List.length _27176 t) = (@List.length _27178 t').
Proof. exact (h1). Qed.
Lemma lem1156543 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1156544 {_27176 _27178 : Type'} (t : list _27176) (t' : list _27178) (h1 : (@List.length _27176 t) = (@List.length _27178 t')) : (term162 _27176 t) = (term162 _27178 t').
Proof. exact (MK_COMB (@lem1156543) (@lem1156542 _27176 _27178 t t' h1)). Qed.
Lemma lem1156545 {_27178 : Type'} (t' : list _27178) : (@List.length _27178 t') = (@List.length _27178 t').
Proof. exact (eq_refl (@List.length _27178 t')). Qed.
Lemma lem1156546 {_27176 _27178 : Type'} (t : list _27176) (t' : list _27178) (h1 : (@List.length _27176 t) = (@List.length _27178 t')) : ((@List.length _27176 t) = (@List.length _27178 t')) = ((@List.length _27178 t') = (@List.length _27178 t')).
Proof. exact (MK_COMB (@lem1156544 _27176 _27178 t t' h1) (@lem1156545 _27178 t')). Qed.
Lemma lem1156548 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1156549 (x : nat) : (x = x) = True.
Proof. exact (@lem1156548 nat x). Qed.
Lemma lem1156550 {_27178 : Type'} (t' : list _27178) : ((@List.length _27178 t') = (@List.length _27178 t')) = True.
Proof. exact (@lem1156549 (@List.length _27178 t')). Qed.
Lemma lem1156551 {_27176 _27178 : Type'} (t : list _27176) (t' : list _27178) (h1 : (@List.length _27176 t) = (@List.length _27178 t')) : ((@List.length _27176 t) = (@List.length _27178 t')) = True.
Proof. exact (TRANS (@lem1156546 _27176 _27178 t t' h1) (@lem1156550 _27178 t')). Qed.
Lemma lem1156552 {_27176 _27178 : Type'} (t : list _27176) (t' : list _27178) (h1 : (@List.length _27176 t) = (@List.length _27178 t')) : True = ((@List.length _27176 t) = (@List.length _27178 t')).
Proof. exact (SYM (@lem1156551 _27176 _27178 t t' h1)). Qed.
Lemma lem1156553 {_27176 _27178 : Type'} (t : list _27176) (t' : list _27178) (h1 : (@List.length _27176 t) = (@List.length _27178 t')) : (@List.length _27176 t) = (@List.length _27178 t').
Proof. exact (EQ_MP (@lem1156552 _27176 _27178 t t' h1) (@lem0)). Qed.
Lemma lem1156554 {_27176 _27178 : Type'} (t : list _27176) (t' : list _27178) (h1 : term8 _27176 _27178 t) (h2 : (@List.length _27176 t) = (@List.length _27178 t')) : (term147 _27176 _27178 t t') = (@List.length _27178 t').
Proof. exact (@lem1156538 _27176 _27178 t' t h1 (@lem1156553 _27176 _27178 t t' h2)). Qed.
Lemma lem1156555 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem1156556 {_27176 _27178 : Type'} (t : list _27176) (t' : list _27178) (h1 : term8 _27176 _27178 t) (h2 : (@List.length _27176 t) = (@List.length _27178 t')) : (term161 _27176 _27178 t t') = (term114 _27178 t').
Proof. exact (MK_COMB (@lem1156555) (@lem1156554 _27176 _27178 t t' h1 h2)). Qed.
Lemma lem1156557 {_27176 _27178 : Type'} (h : _27176) (h' : _27178) (t : list _27176) (t' : list _27178) (h1 : term8 _27176 _27178 t) (h2 : (@List.length _27176 t) = (@List.length _27178 t')) : (term158 _27176 _27178 h h' t t') = (term114 _27178 t').
Proof. exact (TRANS (@lem1156534 _27176 _27178 h h' t t') (@lem1156556 _27176 _27178 t t' h1 h2)). Qed.
Lemma lem1156558 {_27176 _27178 : Type'} (h : _27176) (h' : _27178) (t : list _27176) (t' : list _27178) (h1 : term8 _27176 _27178 t) (h2 : (@List.length _27176 t) = (@List.length _27178 t')) : (term149 _27176 _27178 h t h' t') = (term114 _27178 t').
Proof. exact (TRANS (@lem1156530 _27176 _27178 h h' t t') (@lem1156557 _27176 _27178 h h' t t' h1 h2)). Qed.
Lemma lem1156559 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1156560 {_27176 _27178 : Type'} (h : _27176) (h' : _27178) (t : list _27176) (t' : list _27178) (h1 : term8 _27176 _27178 t) (h2 : (@List.length _27176 t) = (@List.length _27178 t')) : (term163 _27176 _27178 h t h' t') = (term135 _27178 t').
Proof. exact (MK_COMB (@lem1156559) (@lem1156558 _27176 _27178 h h' t t' h1 h2)). Qed.
Lemma lem1156562 {A : Type'} (h : A) (t : list A) : (term113 A h t) = (term114 A t).
Proof. exact (EQ_MP (@lem1156467 A h t) (@lem1156466 A h t)). Qed.
Lemma lem1156563 {_27178 : Type'} (h : _27178) (t : list _27178) : (term113 _27178 h t) = (term114 _27178 t).
Proof. exact (@lem1156562 _27178 h t). Qed.
Lemma lem1156564 {_27178 : Type'} (h' : _27178) (t' : list _27178) : (term113 _27178 h' t') = (term114 _27178 t').
Proof. exact (@lem1156563 _27178 h' t'). Qed.
Lemma lem1156565 {_27176 _27178 : Type'} (h : _27176) (h' : _27178) (t : list _27176) (t' : list _27178) (h1 : term8 _27176 _27178 t) (h2 : (@List.length _27176 t) = (@List.length _27178 t')) : ((term149 _27176 _27178 h t h' t') = (term113 _27178 h' t')) = ((term114 _27178 t') = (term114 _27178 t')).
Proof. exact (MK_COMB (@lem1156560 _27176 _27178 h h' t t' h1 h2) (@lem1156564 _27178 h' t')). Qed.
Lemma lem1156567 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem1156442 m n) (@lem1156441 m n)). Qed.
Lemma lem1156568 {_27178 : Type'} (t' : list _27178) : ((term114 _27178 t') = (term114 _27178 t')) = ((@List.length _27178 t') = (@List.length _27178 t')).
Proof. exact (@lem1156567 (@List.length _27178 t') (@List.length _27178 t')). Qed.
Lemma lem1156570 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1156571 (x : nat) : (x = x) = True.
Proof. exact (@lem1156570 nat x). Qed.
Lemma lem1156572 {_27178 : Type'} (t' : list _27178) : ((@List.length _27178 t') = (@List.length _27178 t')) = True.
Proof. exact (@lem1156571 (@List.length _27178 t')). Qed.
Lemma lem1156573 {_27178 : Type'} (t' : list _27178) : ((term114 _27178 t') = (term114 _27178 t')) = True.
Proof. exact (TRANS (@lem1156568 _27178 t') (@lem1156572 _27178 t')). Qed.
Lemma lem1156574 {_27176 _27178 : Type'} (h : _27176) (h' : _27178) (t : list _27176) (t' : list _27178) (h1 : term8 _27176 _27178 t) (h2 : (@List.length _27176 t) = (@List.length _27178 t')) : ((term149 _27176 _27178 h t h' t') = (term113 _27178 h' t')) = True.
Proof. exact (TRANS (@lem1156565 _27176 _27178 h h' t t' h1 h2) (@lem1156573 _27178 t')). Qed.
Lemma lem1156575 {_27176 _27178 : Type'} (h : _27176) (h' : _27178) (t' : list _27178) (t : list _27176) (h1 : term8 _27176 _27178 t) : term164 _27176 _27178 h t h' t'.
Proof. exact (fun h0 : (@List.length _27176 t) = (@List.length _27178 t') => @lem1156574 _27176 _27178 h h' t t' h1 h0). Qed.
Lemma lem1156576 {_27176 _27178 : Type'} (h : _27176) (h' : _27178) (t : list _27176) (t' : list _27178) : term165 _27176 _27178 h h' t t'.
Proof. exact (@lem1156521 _27176 _27178 h h' t t' True). Qed.
Lemma lem1156577 {_27176 _27178 : Type'} (h : _27176) (h' : _27178) (t' : list _27178) (t : list _27176) (h1 : term8 _27176 _27178 t) : (term71 _27176 _27178 h t h' t') = (term166 _27176 _27178 t t').
Proof. exact (@lem1156576 _27176 _27178 h h' t t' (@lem1156575 _27176 _27178 h h' t' t h1)). Qed.
Lemma lem1156581 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1156582 {_27176 _27178 : Type'} (t : list _27176) (t' : list _27178) : (term166 _27176 _27178 t t') = True.
Proof. exact (@lem1156581 ((@List.length _27176 t) = (@List.length _27178 t'))). Qed.
Lemma lem1156583 {_27176 _27178 : Type'} (h : _27176) (h' : _27178) (t' : list _27178) (t : list _27176) (h1 : term8 _27176 _27178 t) : (term71 _27176 _27178 h t h' t') = True.
Proof. exact (TRANS (@lem1156577 _27176 _27178 h h' t' t h1) (@lem1156582 _27176 _27178 t t')). Qed.
Lemma lem1156584 {_27176 _27178 : Type'} (h : _27176) (h' : _27178) (t' : list _27178) (t : list _27176) (h1 : term8 _27176 _27178 t) : True = (term71 _27176 _27178 h t h' t').
Proof. exact (SYM (@lem1156583 _27176 _27178 h h' t' t h1)). Qed.
Lemma lem1156585 {_27176 _27178 : Type'} (h : _27176) (h' : _27178) (t' : list _27178) (t : list _27176) (h1 : term8 _27176 _27178 t) : term71 _27176 _27178 h t h' t'.
Proof. exact (EQ_MP (@lem1156584 _27176 _27178 h h' t' t h1) (@lem0)). Qed.
Lemma lem1156586 {_27176 _27178 : Type'} (h : _27176) (h' : _27178) (t' : list _27178) (t : list _27176) (h1 : term8 _27176 _27178 t) : term73 _27176 _27178 h t h' t'.
Proof. exact (fun h0 : term67 _27176 _27178 h t t' => @lem1156585 _27176 _27178 h h' t' t h1). Qed.
Lemma lem1156591 {_27176 _27178 : Type'} (h : _27176) (h' : _27178) (t : list _27176) (h1 : term8 _27176 _27178 t) : term77 _27176 _27178 h t h'.
Proof. exact (fun t' : list _27178 => @lem1156586 _27176 _27178 h h' t' t h1). Qed.
Lemma lem1156596 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) (h1 : term8 _27176 _27178 t) : term81 _27176 _27178 h t.
Proof. exact (fun h' : _27178 => @lem1156591 _27176 _27178 h h' t h1). Qed.
Lemma lem1156597 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) (h1 : term8 _27176 _27178 t) : term83 _27176 _27178 h t.
Proof. exact (conj (@lem1156437 _27176 _27178 h t) (@lem1156596 _27176 _27178 h t h1)). Qed.
Lemma lem1156598 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) (h1 : term8 _27176 _27178 t) : term12 _27176 _27178 h t.
Proof. exact (@lem1156142 _27176 _27178 h t (@lem1156597 _27176 _27178 h t h1)). Qed.
Lemma lem1156599 {_27176 _27178 : Type'} (h : _27178) (t : list _27178) : term44 _27176 _27178 h t.
Proof. exact (fun h0 : term38 _27176 _27178 t => @lem1156342 _27176 _27178 h t). Qed.
Lemma lem1156604 {_27176 _27178 : Type'} (h : _27178) : term48 _27176 _27178 h.
Proof. exact (fun t : list _27178 => @lem1156599 _27176 _27178 h t). Qed.
Lemma lem1156609 {_27176 _27178 : Type'} : term52 _27176 _27178.
Proof. exact (fun h : _27178 => @lem1156604 _27176 _27178 h). Qed.
Lemma lem1156610 {_27176 _27178 : Type'} : term54 _27176 _27178.
Proof. exact (conj (@lem1156250 _27176 _27178) (@lem1156609 _27176 _27178)). Qed.
Lemma lem1156611 {_27176 _27178 : Type'} : term4 _27176 _27178.
Proof. exact (@lem1156110 _27176 _27178 (@lem1156610 _27176 _27178)). Qed.
Lemma lem1156612 {_27176 _27178 : Type'} (h : _27176) (t : list _27176) : term14 _27176 _27178 h t.
Proof. exact (fun h0 : term8 _27176 _27178 t => @lem1156598 _27176 _27178 h t h0). Qed.
Lemma lem1156617 {_27176 _27178 : Type'} (h : _27176) : term18 _27176 _27178 h.
Proof. exact (fun t : list _27176 => @lem1156612 _27176 _27178 h t). Qed.
Lemma lem1156622 {_27176 _27178 : Type'} : term22 _27176 _27178.
Proof. exact (fun h : _27176 => @lem1156617 _27176 _27178 h). Qed.
Lemma lem1156623 {_27176 _27178 : Type'} : term24 _27176 _27178.
Proof. exact (conj (@lem1156611 _27176 _27178) (@lem1156622 _27176 _27178)). Qed.
Lemma lem1156624 {_27176 _27178 : Type'} : term29 _27176 _27178.
Proof. exact (@lem1156082 _27176 _27178 (@lem1156623 _27176 _27178)). Qed.
