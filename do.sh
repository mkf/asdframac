#!/usr/bin/env bash
[[ -z $IN_WHAT ]] && IN_WHAT=docker
[[ -z $THE_ENV ]] &&
    case "$IN_WHAT" in
	env) THE_ENV=env ;;
	docker) THE_ENV=(docker run dalej) ;;
	*) THE_ENV=false ;;
    esac
[[ -z $BUILD_THE_ENV ]] &&
    case "$IN_WHAT" in
	env) BUILD_THE_ENV= ;;
	docker) BUILD_THE_ENV=(docker build dalej) ;;
	*) BUILD_THE_ENV=false ;;
    esac
case "$1" in
    build) "${BUILD_THE_ENV[@]}" ;;
    run) "${THE_ENV[@]}" $2 ;;
    *) echo "za \$1 należy dać build, a potem run i za \$2 4zn kod zadania"
       exit 2 ;;
esac
