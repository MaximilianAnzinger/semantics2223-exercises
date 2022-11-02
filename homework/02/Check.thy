theory Check
  imports Submission
begin

theorem enc_dec: "rldec (rlenc a 0 l) = l"
  by (rule Submission.enc_dec)

theorem semantics_unchanged: "aval (normalize a) s = aval a s"
  by (rule Submission.semantics_unchanged)

theorem normalize_normalizes: "normal (normalize a)"
  by (rule Submission.normalize_normalizes)

end