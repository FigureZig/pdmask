(* decision.ml — weighted sum vs threshold.

   Sums the weights of the evidence collected for a candidate span and
   compares against a threshold T (default 50). If the score >= T, the span is
   masked; otherwise it is rejected (not PII).

   Each PII type has a base weight (the "shape" signal) that is added on top
   of the evidence. This matches the canonical cases in the spec (section 5.4):
   a card alone is 30 + 45 (E_CHECKSUM), a date alone is 25 + 35 (E_WHOLE),
   a pin alone is 15 + 40 (E_KW_NEAR), etc. The base weight *is* the signal
   that the rule fired, so there is no separate evidence for "a name was
   recognised": that would count the dictionary hit twice and put "поэт
   Александр Пушкин" back over the threshold.

   The decision also produces a trace: the evidence codes that fired, which is
   what /explain returns. *)

type decision =
  { score : int;
    masked : bool;
    evidence : Evidence.evidence list
  }

let threshold = 50

(* Base weight per PII type (the "shape" signal). *)
let base_weight (ty : Spans.ty) : int =
  match ty with
  (* 40, а не 45. Одинокое словарное слово с заглавной буквы набирало ровно
     порог: 45 + E_CAPS 5 = 50. С подрезанным словарём это почти не всплывало,
     а со склоняемыми формами OpenCorpora — постоянно: «Дону» из
     «Ростов-на-Дону» маскировалось как ФИО и своим E_COOCCUR тянуло за собой
     весь адрес отделения банка. Настоящее ФИО теперь опирается не на
     заглавную букву, а на форму (E_FORM): два словарных слова подряд, три
     слова или отчество. *)
  | Spans.Fio -> 45
  | Spans.Card -> 30
  | Spans.Birth_date -> 25
  | Spans.Issue_date -> 25
  | Spans.Pin -> 15
  | Spans.Cvv -> 15
  | Spans.Phone -> 30
  | Spans.Address -> 40
  | Spans.Passport -> 40
  | Spans.Driver_license -> 40
  | Spans.Inn -> 40
  | Spans.Dept_code -> 40
  (* An email token is a personal identifier on its own; it needs no context,
     unlike a bare digit run. *)
  | Spans.Email -> 55
  | Spans.Card_holder -> 30
  | Spans.Birth_place -> 25
  | Spans.Citizenship -> 25
  | Spans.Issuer -> 25
  (* документы сверх паспорта РФ: форма жёсткая, у СНИЛС есть контрольная
     сумма, поэтому база как у паспорта *)
  | Spans.Snils -> 40
  | Spans.Oms -> 40
  | Spans.Foreign_passport -> 40

(* Decide whether a span is PII given its type and evidence.

   E_ORGADDR — запрет, а не вес. Адрес отделения банка по разделу 5.4 ТЗ не
   является персональными данными клиента ни при каких обстоятельствах, и
   доказательство выдаётся только когда адрес совпал со справочником отделений
   И не содержит номера квартиры. Пока это был просто минус семьдесят, его
   перебивала сумма остальных: на «Отделение банка: г. Ростов-на-Дону, ул.
   Большая Садовая, 1» набиралось 40 базовых + 35 E_COOCCUR + 5 E_CAPS +
   40 E_KW_NEAR + 20 E_FORM - 70 = 70, и адрес отделения уезжал под маску. *)
let decide (ty : Spans.ty) (ev : Evidence.evidence list) : decision =
  let score =
    base_weight ty + List.fold_left (fun acc e -> acc + Evidence.weight e.Evidence.code) 0 ev
  in
  let vetoed = List.exists (fun e -> e.Evidence.code = Evidence.E_ORGADDR) ev in
  {score; masked = (not vetoed) && score >= threshold; evidence = ev}
