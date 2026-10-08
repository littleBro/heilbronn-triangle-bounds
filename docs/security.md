# Repository security and publication

The repository remains private. The following controls were checked through
GitHub's API on 2026-10-08; settings can change independently of this file.

## Configured controls

- Actions are limited to actions/checkout, actions/setup-python and
  actions/upload-artifact. GitHub requires full commit SHA pins. Version updates
  within those repositories still require review; an allowed source is not a
  guarantee that every revision is safe.
- The default workflow token is read-only, and workflows cannot approve pull
  requests. The workflow explicitly grants only contents: read, and checkout
  does not persist credentials.
- Only GitHub-hosted Ubuntu runners are used. There are no repository Actions
  secrets, variables, environments, self-hosted runners, deploy keys or webhooks.
  The owner is the only collaborator. External workflows cannot access this
  private repository's actions or reusable workflows.
- Private-fork pull-request workflows are disabled. Sending write tokens or
  secrets and variables to those workflows is disabled as well.
- New logs and artifacts are retained for 14 days. The workflow also sets a
  14-day artifact lifetime. Earlier artifacts keep their original expiry.
- Superseded runs for the same pull request or ref are cancelled. The secret
  scan has a five-minute job limit; proof verification has a fifteen-minute
  limit. Push checks target main, and pull-request checks target main.
- Dependabot alerts and security-update pull requests are enabled. Weekly
  GitHub Actions version-update pull requests are configured, with no automatic
  merge. Advisory coverage is incomplete for SHA-pinned actions; review version
  updates too. Downloaded Gitleaks and elan releases, and the Lean toolchain,
  require separate manual version and checksum review.

## Secret scanning and verification

The secrets job downloads Gitleaks 8.30.1 from its official release and verifies
the archive SHA-256 before execution. It checks the full fetched Git history
and the checked-out files, using the scanner's built-in rules with no repository
baseline or ignore file. Inline gitleaks:allow comments do not suppress findings.
Potential secret values are redacted in output, and a finding fails the job.
Proof verification runs only after this scan succeeds.

The local pre-publication scan covers all local Git refs and the working tree.
Actions logs and report artifacts also need review before publication: they are
not part of the checked-in Git history. A clean scan is evidence for the rules
and files checked, not proof that every kind of confidential information is absent.

Action commits and downloaded installer archives are pinned. Downloading the
selected Lean toolchain still trusts elan and Lean's release infrastructure.
The Actions allowlist governs uses: entries; it does not restrict arbitrary
commands or network access inside a run.

## Reviewing contributions

Read workflow, script, toolchain and Lean changes before approving a run or
executing them locally. Python and Lean inputs can execute code. A local run
can reach personal GitHub credentials and other files available to that account.
Use an isolated environment without personal credentials for unfamiliar code.

The workflow uses pull_request, not pull_request_target or workflow_run, and
does not use self-hosted runners, deployment credentials or shared build caches.
Keep this boundary when changing CI. A passing check does not make a changed
workflow trustworthy: review the submitted workflow and all files it executes.
CODEOWNERS routes review to @littleBro; it does not enforce review by itself.

## Remaining publication steps

GitHub currently rejects branch protection and rulesets for this private
repository on its account plan. It also rejects the public-fork approval setting
while the repository is private. These controls are not yet enforced.

When the owner explicitly authorizes publication:

1. Recheck secrets, Git history, commit metadata, Actions logs and artifacts on
   the exact revision to publish. Disable Actions briefly during the transition.
2. Change visibility to public. Enable approval for **all external contributors**
   before re-enabling Actions; do not allow unreviewed fork runs automatically.
3. Protect main: require a pull request, require successful secrets and verify
   checks from GitHub Actions on an up-to-date branch, require resolved review
   conversations, and block force pushes and deletion. Apply protection to the
   owner as well. With one maintainer, do not require an unavailable second
   person's approval; human review of external changes remains the owner's job.
4. Verify GitHub secret scanning and push protection, and enable private
   vulnerability reporting. Do not assume visibility changes enabled every
   setting. Read back each effective policy and re-enable Actions only after
   the intended restrictions are confirmed.
5. Confirm account two-factor authentication or a passkey and retain recovery
   codes securely. Repository APIs did not establish the account's 2FA status.

Public commits, logs and forks may be copied. Making a repository private later
does not recall those copies. Visibility is therefore a separate owner decision.

References: [GitHub Actions security](https://docs.github.com/en/actions/reference/security/secure-use),
[repository Actions settings](https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/enabling-features-for-your-repository/managing-github-actions-settings-for-a-repository),
[protected branches](https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/managing-protected-branches/about-protected-branches),
and [Gitleaks](https://github.com/gitleaks/gitleaks).
