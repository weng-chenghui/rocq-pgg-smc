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

expected_concurrency = {
  "group" => "flattened-release-${{ github.sha }}",
  "cancel-in-progress" => false
}
unless workflow.fetch("concurrency") == expected_concurrency
  raise "wrong concurrency: #{workflow.fetch("concurrency").inspect}"
end

jobs = workflow.fetch("jobs")
unless jobs.keys == ["flatten-source", "publish-image"]
  raise "unexpected jobs: #{jobs.keys.inspect}"
end

source_job = jobs.fetch("flatten-source")
image_job = jobs.fetch("publish-image")
raise "wrong source runner" unless source_job.fetch("runs-on") == "ubuntu-latest"
raise "source job must not have a container" if source_job.key?("container")
raise "source job must not depend on another job" if source_job.key?("needs")
raise "source job needs release permission" unless \
  source_job.fetch("permissions") == {"contents" => "write"}
raise "wrong image runner" unless image_job.fetch("runs-on") == "ubuntu-latest"
raise "image job must wait for source release" unless image_job.fetch("needs") == "flatten-source"
raise "image job must not run inside a container" if image_job.key?("container")
expected_image_permissions = {"contents" => "write", "packages" => "write"}
unless image_job.fetch("permissions") == expected_image_permissions
  raise "wrong image permissions: #{image_job.fetch("permissions").inspect}"
end

source_uses = source_job.fetch("steps").map { |step| step["uses"] }.compact
expected_source_uses = [
  "actions/checkout@d23441a48e516b6c34aea4fa41551a30e30af803",
  "actions/upload-artifact@043fb46d1a93c77aae656e7c1c64a875d1fc6a0a"
]
unless source_uses == expected_source_uses
  raise "wrong source action references: #{source_uses.inspect}"
end

image_uses = image_job.fetch("steps").map { |step| step["uses"] }.compact
expected_image_uses = [
  "actions/checkout@d23441a48e516b6c34aea4fa41551a30e30af803"
]
unless image_uses == expected_image_uses
  raise "wrong image action references: #{image_uses.inspect}"
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
raise "missing source Actions artifact" unless source_upload

create_index = source_steps.index { |step| step["name"] == "Create flattened source archive" }
release_index = source_steps.index { |step| step["name"] == "Publish source release" }
upload_index = source_steps.index { |step| step["name"] == "Upload flattened source archive" }
raise "missing source creation step" unless create_index
raise "missing source release step" unless release_index
raise "missing source artifact upload step" unless upload_index
unless create_index < release_index && release_index < upload_index
  raise "source release must be published immediately after flattening"
end

image_commands = image_job.fetch("steps").map { |step| step["run"] }.compact.join("\n")
%w[docker\ login docker\ build docker\ push].each do |fragment|
  raise "missing image command: #{fragment}" unless image_commands.include?(fragment.tr('\\', ''))
end
raise "compiled tar helper is obsolete in CI" if image_commands.include?("build_flat_artifact.sh")
raise "built tar must not be uploaded" if workflow_text.include?("pgg-smc-built-${{ github.sha }}")

required_text = [
  "$GITHUB_SHA",
  "ghcr.io/${GITHUB_REPOSITORY}:${GITHUB_SHA}",
  "--build-arg ROCQ_JOBS=1",
  "scripts/publish_commit_release.sh source",
  "scripts/publish_commit_release.sh image",
  "gh release download",
  "wadt2026-$GITHUB_SHA",
  "source_archive_path",
  "-flat.tar.gz",
  "image_digest",
  "%ct",
  "date -u",
  "if-no-files-found: error"
]
missing = required_text.reject { |fragment| workflow_text.include?(fragment) }
raise "missing workflow text: #{missing.join(", ")}" unless missing.empty?

puts "flattened_build_workflow_test: PASS"
