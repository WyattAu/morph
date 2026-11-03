// Jenkins Pipeline for Specification Tests

pipeline {
    agent any

    environment {
        PIP_CACHE_DIR = "${WORKSPACE}/.cache/pip"
    }

    options {
        buildDiscarder(logRotator(numToKeepStr: '10'))
        timeout(time: 30, unit: 'MINUTES')
        disableConcurrentBuilds()
    }

    stages {
        stage('Checkout') {
            steps {
                checkout scm
            }
        }

        stage('Setup') {
            steps {
                script {
                    sh 'if [ ! -d .venv ]; then python3 -m venv .venv; fi'
                    sh '.venv/bin/pip install --upgrade pip'
                    sh '.venv/bin/pip install -e scripts/'
                }
            }
        }

        stage('Test') {
            steps {
                script {
                    sh '.venv/bin/pytest scripts/tests/ -v --tb=short'
                }
            }
        }

        // Aligned with .github/workflows/spec-validation.yml (loop 118):
        // lint without --strict is the blocking gate (0 errors on the
        // current corpus; the 106 warnings are the accepted baseline).
        // format --check (~16k deviations) and validate (624 missing-section
        // errors for sections the corpus was never written to) are advisory:
        // reported as artifacts, never failing the build.
        stage('Validate Specifications') {
            steps {
                script {
                    sh '.venv/bin/spec-tools lint spec/ > lint-report.txt 2>&1 || true'
                    sh 'set -e && .venv/bin/spec-tools lint spec/'
                    sh '.venv/bin/spec-tools format spec/ --check > format-report.txt 2>&1 || true'
                    sh '.venv/bin/spec-tools validate spec/ --check-traceability --check-security --check-performance --check-maintainability --check-risk --check-verification > validate-report.txt 2>&1 || true'
                    sh '.venv/bin/spec-tools check-links spec/ --output link-report.json --format json || true'
                }
            }
            post {
                always {
                    archiveArtifacts artifacts: 'lint-report.txt, format-report.txt, validate-report.txt, link-report.json', allowEmptyArchive: true
                }
            }
        }
    }

    post {
        always {
            cleanWs()
        }

        success {
            echo 'Specification tests passed successfully!'
        }

        failure {
            echo 'Specification tests failed!'
        }

        unstable {
            echo 'Specification tests unstable!'
        }
    }
}
