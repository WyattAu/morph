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

        stage('Validate Specifications') {
            steps {
                script {
                    sh 'set -e && .venv/bin/spec-tools format spec/ --check'
                    sh 'set -e && .venv/bin/spec-tools lint spec/ --strict'
                    sh 'set -e && .venv/bin/spec-tools validate spec/ --check-traceability --check-security --check-performance --check-maintainability --check-risk --check-verification'
                    sh '.venv/bin/spec-tools check-links spec/ --output link-report.json --format json || true'
                }
            }
            post {
                always {
                    archiveArtifacts artifacts: 'link-report.json', allowEmptyArchive: true
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
