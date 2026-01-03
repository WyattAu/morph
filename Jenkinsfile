// Jenkins Pipeline for Specification Tests

pipeline {
    agent any
    
    environment {
        PIP_CACHE_DIR = "${WORKSPACE}/.cache/pip"
        COVERAGE_THRESHOLD = '80'
    }
    
    options {
        // Keep last 10 builds
        buildDiscarder(logRotator(numToKeepStr: '10'))
        // Timeout after 30 minutes
        timeout(time: 30, unit: 'MINUTES')
        // Disable concurrent builds
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
                    // Detect Python version
                    def pythonVersion = sh(
                        script: 'python3 --version 2>&1 | awk \'{print $2}\'',
                        returnStdout: true
                    ).trim()
                    echo "Using Python ${pythonVersion}"
                    
                    // Create virtual environment
                    sh 'python3 -m venv venv'
                    
                    // Activate virtual environment
                    sh '. venv/bin/activate'
                    
                    // Upgrade pip
                    sh 'pip install --upgrade pip'
                    
                    // Install dependencies
                    sh 'pip install -r tests/requirements.txt'
                }
            }
        }
        
        stage('Lint') {
            steps {
                script {
                    sh '. venv/bin/activate && pylint tests/specification_test_suite.py --exit-zero'
                }
            }
        }
        
        stage('Type Check') {
            steps {
                script {
                    sh '. venv/bin/activate && mypy tests/specification_test_suite.py --ignore-missing-imports'
                }
            }
        }
        
        stage('Test') {
            parallel {
                stage('Test Python 3.8') {
                    agent { label 'python38' }
                    steps {
                        script {
                            sh '''
                                . venv/bin/activate
                                cd tests
                                pytest specification_test_suite.py -v \
                                    --cov=tests \
                                    --cov-report=xml \
                                    --cov-report=html \
                                    --cov-fail-under=${COVERAGE_THRESHOLD} \
                                    --junitxml=test-results.xml
                            '''
                        }
                    }
                    post {
                        always {
                            junit 'tests/test-results.xml'
                            publishHTML(target: [
                                reportDir: 'tests/htmlcov',
                                reportFiles: 'index.html',
                                reportName: 'Coverage Report (Python 3.8)',
                                keepAll: true,
                                allowMissing: false
                            ])
                        }
                    }
                }
                
                stage('Test Python 3.9') {
                    agent { label 'python39' }
                    steps {
                        script {
                            sh '''
                                . venv/bin/activate
                                cd tests
                                pytest specification_test_suite.py -v \
                                    --cov=tests \
                                    --cov-report=xml \
                                    --cov-report=html \
                                    --cov-fail-under=${COVERAGE_THRESHOLD} \
                                    --junitxml=test-results.xml
                            '''
                        }
                    }
                    post {
                        always {
                            junit 'tests/test-results.xml'
                            publishHTML(target: [
                                reportDir: 'tests/htmlcov',
                                reportFiles: 'index.html',
                                reportName: 'Coverage Report (Python 3.9)',
                                keepAll: true,
                                allowMissing: false
                            ])
                        }
                    }
                }
                
                stage('Test Python 3.10') {
                    agent { label 'python310' }
                    steps {
                        script {
                            sh '''
                                . venv/bin/activate
                                cd tests
                                pytest specification_test_suite.py -v \
                                    --cov=tests \
                                    --cov-report=xml \
                                    --cov-report=html \
                                    --cov-fail-under=${COVERAGE_THRESHOLD} \
                                    --junitxml=test-results.xml
                            '''
                        }
                    }
                    post {
                        always {
                            junit 'tests/test-results.xml'
                            publishHTML(target: [
                                reportDir: 'tests/htmlcov',
                                reportFiles: 'index.html',
                                reportName: 'Coverage Report (Python 3.10)',
                                keepAll: true,
                                allowMissing: false
                            ])
                        }
                    }
                }
                
                stage('Test Python 3.11') {
                    agent { label 'python311' }
                    steps {
                        script {
                            sh '''
                                . venv/bin/activate
                                cd tests
                                pytest specification_test_suite.py -v \
                                    --cov=tests \
                                    --cov-report=xml \
                                    --cov-report=html \
                                    --cov-fail-under=${COVERAGE_THRESHOLD} \
                                    --junitxml=test-results.xml
                            '''
                        }
                    }
                    post {
                        always {
                            junit 'tests/test-results.xml'
                            publishHTML(target: [
                                reportDir: 'tests/htmlcov',
                                reportFiles: 'index.html',
                                reportName: 'Coverage Report (Python 3.11)',
                                keepAll: true,
                                allowMissing: false
                            ])
                        }
                    }
                }
            }
        }
        
        stage('Validate Specifications') {
            steps {
                script {
                    // Install spec-tools package
                    sh '. venv/bin/activate && pip install -e scripts/'
                    
                    // Run format check
                    sh '. venv/bin/activate && spec-tools format spec/ --check'
                    
                    // Run lint with strict mode
                    sh '. venv/bin/activate && spec-tools lint spec/ --strict'
                    
                    // Run validation with all checks
                    sh '. venv/bin/activate && spec-tools validate spec/ --check-traceability --check-security --check-performance --check-maintainability --check-risk --check-verification'
                    
                    // Run link check and save report
                    sh '. venv/bin/activate && spec-tools check-links spec/ --output link-report.json --format json'
                }
            }
            post {
                always {
                    // Archive link report
                    archiveArtifacts artifacts: 'link-report.json', allowEmptyArchive: true
                }
            }
        }
        
        stage('Security Scan') {
            parallel {
                stage('Bandit') {
                    steps {
                        script {
                            sh '''
                                . venv/bin/activate
                                pip install bandit[toml]
                                bandit -r tests/ -f json -o bandit-report.json || true
                                bandit -r tests/ -f txt -o bandit-report.txt || true
                            '''
                        }
                    }
                    post {
                        always {
                            archiveArtifacts artifacts: 'bandit-report.*', allowEmptyArchive: true
                        }
                    }
                }
                
                stage('Safety') {
                    steps {
                        script {
                            sh '''
                                . venv/bin/activate
                                pip install safety
                                safety check --file tests/requirements.txt --json --output safety-report.json || true
                                safety check --file tests/requirements.txt --output safety-report.txt || true
                            '''
                        }
                    }
                    post {
                        always {
                            archiveArtifacts artifacts: 'safety-report.*', allowEmptyArchive: true
                        }
                    }
                }
            }
        }
        
        stage('Coverage Report') {
            steps {
                script {
                    sh '''
                        . venv/bin/activate
                        coverage combine tests/coverage.xml
                        coverage report --fail-under=${COVERAGE_THRESHOLD}
                    '''
                }
            }
        }
    }
    
    post {
        always {
            // Clean up workspace
            cleanWs()
        }
        
        success {
            echo 'Specification tests passed successfully!'
            // Send success notification
            // emailext subject: "Specification Tests - SUCCESS",
            //          body: "All specification tests passed.",
            //          to: "team@example.com"
        }
        
        failure {
            echo 'Specification tests failed!'
            // Send failure notification
            // emailext subject: "Specification Tests - FAILED",
            //          body: "Specification tests failed. Check Jenkins logs for details.",
            //          to: "team@example.com"
        }
        
        unstable {
            echo 'Specification tests unstable!'
            // Send unstable notification
            // emailext subject: "Specification Tests - UNSTABLE",
            //          body: "Specification tests are unstable. Check Jenkins logs for details.",
            //          to: "team@example.com"
        }
    }
}

// Helper function to send notifications
def sendNotification(String status) {
    def buildUrl = env.BUILD_URL ?: "N/A"
    def buildNumber = env.BUILD_NUMBER ?: "N/A"
    
    def message = """
        Specification Tests: ${status}
        
        Build: ${buildNumber}
        URL: ${buildUrl}
        
        Check the logs for more details.
    """.strip()
    
    // Add your notification logic here (Slack, email, etc.)
    echo message
}
