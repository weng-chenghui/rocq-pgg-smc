#!/usr/bin/env ruby

require "yaml"

workflow_path = ARGV.fetch(0)
workflow_text = File.read(workflow_path)
workflow = YAML.safe_load(workflow_text, aliases: false)

expected_trigger = {"push" => {"branches" => ["main"]}}
unless workflow.fetch("on") == expected_trigger
  raise "wrong trigger: #{workflow.fetch("on").inspect}"
end

expected_permissions = {"contents" => "read"}
unless workflow.fetch("permissions") == expected_permissions
  raise "wrong permissions: #{workflow.fetch("permissions").inspect}"
end

jobs = workflow.fetch("jobs")
unless jobs.keys == ["flatten-source", "build-flattened"]
  raise "unexpected jobs: #{jobs.keys.inspect}"
end

source_job = jobs.fetch("flatten-source")
build_job = jobs.fetch("build-flattened")
raise "wrong source runner" unless source_job.fetch("runs-on") == "ubuntu-latest"
raise "source job must not have a container" if source_job.key?("container")
raise "source job must not depend on another job" if source_job.key?("needs")
raise "wrong build runner" unless build_job.fetch("runs-on") == "ubuntu-latest"
raise "build job must wait for source artifact" unless build_job.fetch("needs") == "flatten-source"

expected_container = {
  "image" => "mathcomp/mathcomp@sha256:ad95400eeb7f6fecb9d3b85673bf58990ae5800d9a8c41fd533e2f9678754cbc",
  "options" => "--user root",
  "env" => {"OPAMROOT" => "/home/rocq/.opam"}
}
unless build_job.fetch("container") == expected_container
  raise "wrong build container: #{build_job.fetch("container").inspect}"
end

source_uses = source_job.fetch("steps").map { |step| step["uses"] }.compact
expected_source_uses = [
  "actions/checkout@d23441a48e516b6c34aea4fa41551a30e30af803",
  "actions/upload-artifact@043fb46d1a93c77aae656e7c1c64a875d1fc6a0a"
]
unless source_uses == expected_source_uses
  raise "wrong source action references: #{source_uses.inspect}"
end

build_uses = build_job.fetch("steps").map { |step| step["uses"] }.compact
expected_build_uses = [
  "actions/checkout@d23441a48e516b6c34aea4fa41551a30e30af803",
  "actions/download-artifact@37930b1c2abaa49bbe596cd826c3c89aef350131",
  "actions/upload-artifact@043fb46d1a93c77aae656e7c1c64a875d1fc6a0a"
]
unless build_uses == expected_build_uses
  raise "wrong build action references: #{build_uses.inspect}"
end

source_steps = source_job.fetch("steps")
source_commands = source_steps.map { |step| step["run"] }.compact.join("\n")
forbidden_source_commands = %w[opam rocq make]
found_forbidden = forbidden_source_commands.select do |command|
  source_commands.match?(/(^|[^A-Za-z0-9_])#{Regexp.escape(command)}([^A-Za-z0-9_]|$)/)
end
unless found_forbidden.empty?
  raise "source job invokes build tools: #{found_forbidden.join(", ")}"
end

source_upload = source_steps.find { |step| step["uses"]&.start_with?("actions/upload-artifact@") }
build_download = build_job.fetch("steps").find { |step| step["uses"]&.start_with?("actions/download-artifact@") }
raise "source artifact name does not match build input" unless \
  source_upload.fetch("with").fetch("name") == build_download.fetch("with").fetch("name")

steps = build_job.fetch("steps")
trust_index = steps.index { |step| step["name"] == "Trust checked-out repository" }
install_index = steps.index { |step| step["name"] == "Install dependencies" }
raise "missing repository trust step" unless trust_index
raise "missing dependency installation step" unless install_index
raise "repository trust must precede dependency installation" unless trust_index < install_index
trust_command = steps.fetch(trust_index).fetch("run")
unless trust_command == 'git config --global --add safe.directory "$GITHUB_WORKSPACE"'
  raise "wrong repository trust command: #{trust_command.inspect}"
end

required_text = [
  "opam install . --deps-only --yes",
  "$GITHUB_SHA",
  "opam switch show --safe",
  "ROCQ_JOBS=1",
  "scripts/build_flat_artifact.sh",
  "source_archive_path",
  "built_archive_path",
  "-flat.tar.gz",
  "-built.tar.gz",
  "ulimit -s unlimited",
  "%ct",
  "date -u",
  "if-no-files-found: error"
]
missing = required_text.reject { |fragment| workflow_text.include?(fragment) }
raise "missing workflow text: #{missing.join(", ")}" unless missing.empty?

puts "flattened_build_workflow_test: PASS"
